-- Prove2me | Theorems.Thm_UnitalMIP_theorem_3_2
-- name    : UnitalMIP.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:42:19.164904+00:00
-- url     : https://prove2.me/theorems/f1a971bd-fabb-4e91-a163-60ef83cbc849
-- title:
--   Theorem 3.2 — smoothing changes the value by at most $2\sqrt{\frac{\alpha_\psi}{1-\alpha_\psi}w\log(2t)}$
-- statement:
--   Fix a game $G=(\mathcal X,\mathcal Y,\mathcal A,\mathcal B,p_G,V)$ and $n\ge1$, and let $\psi\in M_2\otimes M_2$ be a state with $\psi_A=\psi_B=\mathbb 1/2$ and $\rho_{\max}(\psi)<1$, used through $\psi^{\otimes n}$. Let $\mathcal A,\mathcal B$ be local POVM strategies on $(\mathbb C^2)^{\otimes n}$, $t=\max\{|\mathcal A|,|\mathcal B|\}$, $0<w\le1/4$, and let $u_x,v_y\in[w,2w]$ be arbitrary. With the smoothed POVMs $A^{x,u_x}_a=\mathcal T_{u_x}(A^x_a)$ and $B^{y,v_y}_b=\mathcal T_{v_y}(B^y_b)$,
--
--   $$
--   \bigl|\mathrm{Val}_G(\mathcal A,\mathcal B)-\mathrm{Val}_G(\mathcal A^{(u)},\mathcal B^{(v)})\bigr|\le 2\sqrt{\frac{\alpha_\psi}{1-\alpha_\psi}\,w\log(2t)},
--   $$
--
--   where $0\le\alpha_\psi<1$ is the complete-SDPI constant from Lemma 4.1.
--
--   Smoothing is the first step of the finite-copy approximation: it costs little value and makes the measurements approximately low-degree.
--
--   **Formalization Note** Both values are on $\psi^{\otimes n}$; $\log$ is natural.
--
--   Differences from the source:
--   - generalization: “αψ … the complete-SDPI constant from Lemma 4.1” → every $\alpha\in[0,1)$ with the property of Lemma 4.1 for every canonical form of $\psi$ (`IsCompleteSDPIConst ψ α`); reason: Lemma 4.1 only asserts that such a constant exists, and the proof uses only its inequality; the statement for each such constant specializes to the one Lemma 4.1 supplies
--   - encoding: $\psi^{\otimes n}$ → `tensorPow ψ n`: the same operator with Alice's $n$ registers collected first; reason: a permutation of tensor factors; Alice holds the first qubit of every copy, as in the source
--   - encoding: $\mathrm{Tr}[(A^x_a\otimes(B^y_b)^T)\psi]$ in the value (16), (22) → the real part of this trace; reason: the trace is real for the positive semidefinite families and states to which the source applies the formula
--   - generalization: the §1.1 standing assumption (“Throughout, let ψ be a fixed two-qubit state … and assume that its entries are computable in polynomial time”, p.4) → any two-qubit density matrix ψ with the stated properties, with no computability hypothesis; reason: the statement is purely analytic and holds for every such state; it specializes to the source's claim on every computable ψ
-- source:
--   Dong, Jiang, Qin, Yao, Zhou, A Dichotomy for MIP* in the Presence of Unital Noise, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), Theorem 3.2, p.26

import Mathlib
import Definitions.Def_UnitalMIP_HasMaxMixedMarginals
import Definitions.Def_UnitalMIP_rhoMax
import Definitions.Def_UnitalMIP_omegaInf
import Definitions.Def_UnitalMIP_depolT
import Definitions.Def_UnitalMIP_IsCompleteSDPIConst

open scoped Matrix

namespace UnitalMIP

/-- **Theorem 3.2** (Smoothing; Dong, Jiang, Qin, Yao, Zhou, *A Dichotomy for MIP* in the Presence of Unital Noise*, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), p.26). Fix a game `G = (𝒳, 𝒴, 𝒜, ℬ, p_G, V)` and `n ≥ 1`, and
use the resource state `ψ^{⊗n}`, where `ψ ∈ M₂ ⊗ M₂` satisfies `ψ_A = ψ_B = 𝟙/2` and `ρmax(ψ) < 1`.
Let `𝒜`, `ℬ` be local POVM strategies on `(ℂ²)^{⊗n}`, `t = max{|𝒜|, |ℬ|}`, `0 < w ≤ 1/4`, and
`u_x, v_y ∈ [w, 2w]` arbitrary. Then the smoothed strategies `A^{x,u_x}_a := 𝒯_{u_x}(A^x_a)`,
`B^{y,v_y}_b := 𝒯_{v_y}(B^y_b)` satisfy
`|Val_G(𝒜, ℬ) − Val_G(𝒜^{(u)}, ℬ^{(v)})| ≤ 2 √(α_ψ/(1 − α_ψ) · w log(2t))`,
where `0 ≤ α_ψ < 1` is the complete-SDPI constant from Lemma 4.1.

**Formalization Note** `α_ψ` is any `α ∈ [0, 1)` with the property of Lemma 4.1
(`IsCompleteSDPIConst ψ α`); Lemma 4.1 provides one. Both values are on `ψ^{⊗n}` (`tensorPow`).
`log` is the natural logarithm. -/
theorem theorem_3_2 {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : MIPRE.Game X Y A B) (n : ℕ) (hn : 1 ≤ n)
    (ψ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hψ : QAlgorithms.IsDensityMatrix ψ) (hmm : HasMaxMixedMarginals ψ) (hρ : rhoMax ψ < 1)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hαψ : IsCompleteSDPIConst ψ α)
    (SA : X → MIPRE.POVM A (Fin n → Fin 2)) (SB : Y → MIPRE.POVM B (Fin n → Fin 2))
    (w : ℝ) (hw0 : 0 < w) (hw1 : w ≤ 1 / 4) (u : X → ℝ) (v : Y → ℝ)
    (hu : ∀ x, w ≤ u x ∧ u x ≤ 2 * w) (hv : ∀ y, w ≤ v y ∧ v y ≤ 2 * w) :
    |val G (tensorPow ψ n) (povmMats SA) (povmMats SB) -
        val G (tensorPow ψ n) (fun x a => depolT (u x) n (povmMats SA x a))
          (fun y b => depolT (v y) n (povmMats SB y b))| ≤
      2 * Real.sqrt (α / (1 - α) * w *
        Real.log (2 * (max (Fintype.card A) (Fintype.card B) : ℝ))) := by sorry

end UnitalMIP
