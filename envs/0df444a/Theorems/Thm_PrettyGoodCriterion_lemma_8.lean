-- Prove2me | Theorems.Thm_PrettyGoodCriterion_lemma_8
-- name    : PrettyGoodCriterion.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:32:50.438474+00:00
-- url     : https://prove2.me/theorems/c33b8093-fd22-4a73-8d61-0b5474c7dbe0
-- title:
--   Lemma 8 — the PGM is closed under coarse-graining
-- statement:
--   Let $\mathcal E=\{(\pi_x,\sigma_x):x\in\mathcal X\}$ be a finite ensemble of density matrices ($\pi_x\ge0$, $\sum_x\pi_x=1$) with PGM $\{M_{\hat x}\}$, let $f:\mathcal X\to\mathcal Y$ be a map to a finite set, and let $\mathcal F=\{(\nu_y,\omega_y)\}$ be the pushforward ensemble with PGM $\{N_{\hat y}\}$. Then:
--
--   1. the PGM of $\mathcal F$ is the PGM of $\mathcal E$ followed by $f$:
--   $$N_{\hat y}=\sum_{\hat x:\,f(\hat x)=\hat y}M_{\hat x}\qquad\text{for every }\hat y\in\mathcal Y;$$
--   2. for every $y,\hat y\in\mathcal Y$,
--   $$\Pr[f(x)=y,\ f(\hat x)=\hat y]=\sum_{x:\,f(x)=y}\ \sum_{\hat x:\,f(\hat x)=\hat y}\pi_x\operatorname{Tr}(\sigma_xM_{\hat x})=\nu_y\operatorname{Tr}(\omega_yN_{\hat y});$$
--   3. consequently
--   $$\Pr[f(\hat x)\neq f(x)]=\sum_x\ \sum_{\hat x:\,f(\hat x)\neq f(x)}\pi_x\operatorname{Tr}(\sigma_xM_{\hat x})=p_e(\mathcal F).$$
--
--   Clauses 1–2 make precise the statement that $f(\hat x)$ is the outcome of the PGM of $\mathcal F$ applied to $\omega_{f(x)}$. Applied to a coordinate projection this turns the block PGM of a code into a bitwise PGM (Lemma 9).
--
--   **Formalization Note** Probabilities are real parts of traces. A label $y$ with $\nu_y=0$ has $\omega_y=0$.
--
--   Differences from the source:
--   - reading: 𝒴 an arbitrary set ("any classical map f : 𝒳 → 𝒴") → 𝒴 a finite type; reason: ℱ must be a finite ensemble for p_e(ℱ) to be defined (§2.2 fixes finite ensembles)
--   - encoding: ω_y = E[σ_x | f(x) = y], undefined when ν_y = 0 → ω_y = 0 when ν_y = 0; reason: such y have weight 0 and contribute to no PGM operator and no error term
--   - reading: f(x̂) is the outcome of the PGM of ℱ when applied to ω_{f(x)} → the operator identity N_ŷ = ∑_{f(x̂)=ŷ} M_x̂ together with the joint law Pr[f(x)=y, f(x̂)=ŷ] = ν_y Tr(ω_y N_ŷ); reason: the stronger of the two readings; both are the first two displays of the proof (p.71–72)
--   - encoding: ℂ^d, d × d matrices → matrices indexed by an arbitrary finite type ι; reason: ℂ^d is the case ι = Fin d, and every finite type is Fin d up to relabelling, which changes no trace, product or positivity
--   - encoding: probabilities Tr(σ_x M_x̂) (and the other traces of products of positive semidefinite matrices) → real parts of the traces; reason: these traces are real; taking the real part changes no value
-- source:
--   Alrabiah, Guruswami, Binary code rate bounds via classical–quantum channels, arXiv:2608.09347 (held version, sha256 e6d5ac13…), Lemma 8, p.18 (PDF 20); proof Appendix A.5, pp.71–72 (PDF 73–74)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_PrettyGoodCriterion_pgmError
import Definitions.Def_PrettyGoodCriterion_pushState

open scoped ComplexOrder

namespace PrettyGoodCriterion

/-- **Lemma 8 (PGM is closed under coarse-graining)**, Alrabiah–Guruswami, *Binary code rate
bounds via classical–quantum channels*, arXiv:2608.09347 (held version), p.18 (PDF 20); proof in
Appendix A.5, pp.71–72 (PDF 73–74).

Let `ℰ = {(π_x, σ_x) : x ∈ 𝒳}` be a finite ensemble of density matrices (`π ⩾ 0`, `∑ π = 1`,
§2.2) and `f : 𝒳 → 𝒴` a classical map, with pushforward ensemble `ℱ = {(ν_y, ω_y)}`. Then

1. the PGM of `ℱ` is the post-processing of the PGM of `ℰ` under `f`:
   `N_ŷ = ∑_{x̂ : f(x̂) = ŷ} M_x̂` ("`f(x̂)` is the outcome of the PGM of `ℱ`");
2. the joint law: `Pr[f(x) = y, f(x̂) = ŷ] = ν_y Tr(ω_y N_ŷ)` for all `y, ŷ`;
3. `Pr[f(x̂) ≠ f(x)] = p_e(ℱ)`.

**Formalization Note.** `𝒴` is a finite type (`ℱ` is a finite ensemble, §2.2). States `ω_y` with
`ν_y = 0` are `0` (see `pushState`). Probabilities are real parts of traces. -/
theorem lemma_8 {X Y ι : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [Fintype ι] [DecidableEq ι] (p : X → ℝ) (σ : X → Matrix ι ι ℂ) (hp : ∀ x, 0 ≤ p x)
    (hsum : ∑ x, p x = 1) (hσ : ∀ x, QAlgorithms.IsDensityMatrix (σ x)) (f : X → Y) :
    (∀ yh : Y, pgm (pushPrior p f) (pushState p σ f) yh =
        ∑ xh ∈ Finset.univ.filter (fun xh => f xh = yh), pgm p σ xh) ∧
    (∀ y yh : Y, ∑ x ∈ Finset.univ.filter (fun x => f x = y),
        ∑ xh ∈ Finset.univ.filter (fun xh => f xh = yh), p x * (σ x * pgm p σ xh).trace.re =
        pushPrior p f y *
          (pushState p σ f y * pgm (pushPrior p f) (pushState p σ f) yh).trace.re) ∧
    (∑ x, ∑ xh ∈ Finset.univ.filter (fun xh => f xh ≠ f x), p x * (σ x * pgm p σ xh).trace.re =
        pgmError (pushPrior p f) (pushState p σ f)) := by sorry

end PrettyGoodCriterion
