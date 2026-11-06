-- Prove2me | Theorems.Thm_RankOneSK_lemma_3_2
-- name    : RankOneSK.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:31:22.71177+00:00
-- url     : https://prove2.me/theorems/30317334-554a-4892-a56d-d22f8529bcd7
-- title:
--   Lemma 3.2 — $\sum_{i\ne j}J_{ij}\mathbb E[M_{ij}L_ifL_jf]=\|J\|_{\mathrm{op}}(\mathcal E(f)-s(2-s)\mathcal D(f))-\mathbb E[w^\top\tilde Jw]$
-- statement:
--   Let $\mu_J$ be the SK Gibbs measure with interaction matrix $J$ (symmetric, zero diagonal, no external field), $L_i=I-P_i$, $\bar X_i=\bar X_i(x_{-i})$ the conditional magnetization, $s\in\mathbb R$ and $f:\{\pm1\}^n\to\mathbb R$. Let $M_{ij}(x)=(x_i+s\bar X_i)(x_j+s\bar X_j)$, $w_i(x)=(x_i+s\bar X_i)\,L_if(x)$, $\tilde J=\|J\|_{\mathrm{op}}I-J$, $\mathcal E(f)=\sum_i\mathbb E[(L_if)^2]$ as in (1) and $\mathcal D(f)=\sum_i\mathbb E[\bar X_i^2(L_if)^2]$ as in (26).
--
--   **Lemma 3.2.**
--   $$\sum_{i\neq j}J_{ij}\,\mathbb E\big[M_{ij}(L_if)(L_jf)\big]=\|J\|_{\mathrm{op}}\big(\mathcal E(f)-s(2-s)\mathcal D(f)\big)-\mathbb E\big[w^\top\tilde Jw\big].$$
--
--   Because $M$ is rank one, the cross terms are a quadratic form in $w$; the identity separates the spectral-norm loss from the positive semidefinite remainder $\mathbb E[w^\top\tilde Jw]$, which Lemma 2.10 then bounds below.
--
--   Differences from the source:
--   - generalization: J the β-GOE matrix of §3, s the parameter of §3 → every interaction J and every s ∈ ℝ; reason: the lemma is a deterministic identity that uses no property of J or s; specializing to the §3 J and s gives the source
--   - encoding: ∥J∥_op, E(f), D(f), wᵀJ̃w → LiqPremiaEq.opNorm of the matrix (coupling J i k), the published dirichlet J 0 f, magDirichlet J f, and the double sum Σ_i Σ_j w_i (∥J∥_op δ_ij − J_ij) w_j; reason: same quantities
--   - encoding: x ∈ {±1}ⁿ, sites i ∈ [n] → configurations Fin n → Bool read as ±1 by spinValue, sites indexed from 0; reason: Lean convention; same objects
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, Lemma 3.2, p.20 (PDF p.21); (1), p.2; (26), p.20

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_RankOneSK_siteLap
import Definitions.Def_RankOneSK_condMag
import Definitions.Def_RankOneSK_magShift
import Definitions.Def_RankOneSK_magDirichlet
import Definitions.Def_LiqPremiaEq_opNorm

open OAI.SKGap MeasureTheory ProbabilityTheory Filter

namespace RankOneSK

/-- **Lemma 3.2.** Let `J̃ = ∥J∥_op I − J` and `w_i(x) = (x_i + sX̄_i(x_{−i}))·L_i f(x)`. Then
`Σ_{i≠j} J_ij E[M_ij (L_i f)(L_j f)] = ∥J∥_op (E(f) − s(2 − s)𝒟(f)) − E[wᵀ J̃ w]`,
where `M_ij = (x_i + sX̄_i(x_{−i}))(x_j + sX̄_j(x_{−j}))`, `E(f) = Σ_i E[(L_i f)²]` (1) and
`𝒟(f) = Σ_i E[X̄_i²(L_i f)²]` (26).

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, Lemma 3.2, p.20; (1), p.2; (26), p.20.

**Formalization Note** Spins are `OAI.SKGap.Spin n = Fin n → Bool` (±1 through `spinValue`), sites 0-based `Fin n`.
The β-GOE matrix `J` is the published `OAI.SKGap.Disorder n` under `disorderLaw β n`: entries
`J_ik`, `i < k`, i.i.d. `N(0, β²/n)`, `coupling J` symmetric with zero diagonal. Expectations under the zero-field SK Gibbs measure. The
identity is deterministic: for every interaction `J`, every `s ∈ ℝ`, every `f`. `E(f)` is the published
`OAI.SKGap.dirichlet J 0 f`; `𝒟(f)` is `magDirichlet J f`; `∥J∥_op` is the `ℓ²` operator norm (the published `LiqPremiaEq.opNorm`) of the
matrix `(coupling J i k)`; `wᵀJ̃w` is written as a double sum. -/
theorem lemma_3_2 {n : ℕ} (J : Disorder n) (s : ℝ) (f : Spin n → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n,
        (if i = j then 0 else
          coupling J i j * expectation J 0 (fun x =>
            magShift J s i x * magShift J s j x * siteLap J i f x * siteLap J j f x)) =
      LiqPremiaEq.opNorm (Matrix.of fun i k => coupling J i k) *
          (dirichlet J 0 f - s * (2 - s) * magDirichlet J f) -
        expectation J 0 (fun x => ∑ i : Fin n, ∑ j : Fin n,
          magShift J s i x * siteLap J i f x *
            ((if i = j then LiqPremiaEq.opNorm (Matrix.of fun i k => coupling J i k) else 0) - coupling J i j) *
            (magShift J s j x * siteLap J j f x)) := by sorry

end RankOneSK
