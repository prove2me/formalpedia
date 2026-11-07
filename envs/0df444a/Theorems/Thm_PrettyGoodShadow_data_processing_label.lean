-- Prove2me | Theorems.Thm_PrettyGoodShadow_data_processing_label
-- name    : PrettyGoodShadow.data_processing_label
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:24:35.287327+00:00
-- url     : https://prove2.me/theorems/98fe9876-199e-42c0-88a0-661b3628d24b
-- title:
--   Proof of Lemma 4.9, display — $D(S(q,n)\|S(p,n))\le D(q\|p)$
-- statement:
--   Let $q,p$ be priors with $\operatorname{supp}(q)\subseteq\operatorname{supp}(p)$. The classical-quantum channel $x\mapsto\rho_x^{\otimes n}$ maps $q$ to $S(q,n)$ and $p$ to $S(p,n)$, and data processing gives
--
--   $$
--   D\big(S(q,n)\,\big\|\,S(p,n)\big)\le D(q\|p).
--   $$
--
--   It closes the telescoping sum in the proof of Lemma 4.9.
--
--   **Formalization Note** The inequality is in the extended reals with the classical value coerced, so it also says that the left side is finite.
--
--   Differences from the source:
--   - generalization: n = 2kT → every natural number n; reason: the channel and the argument do not depend on the form of n, and n = 2kT is one case
--   - encoding: D(S(q,2kT)∥S(p,2kT)) = D(R(q)∥R(p)) ≤ D(q∥p) → the inequality between the outer terms, with S(·,n) written directly; reason: R(q) is S(q,n) by definition of R, so the middle term is the first
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), Proof of Lemma 4.9, p.24

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_DimFreeShadow_recoveryEffect
import Definitions.Def_PrettyGoodShadow_labelRelEntropy

namespace PrettyGoodShadow

open DimFreeShadow (ensembleState)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

/-- **Data processing for the label channel** (arXiv:2610.06781, sha256 bd055b7d…, end of the proof of Lemma 4.9,
p.24). The classical-quantum channel `x ↦ ρ_x^{⊗n}` maps the prior `q` to `S(q, n)`, and
`D(S(q, n) ∥ S(p, n)) ≤ D(q ∥ p)` when `supp(q) ⊆ supp(p)`.

**Formalization Note** The page has `n = 2kT`; the statement holds for every `n`, with the same channel. The
inequality is in `EReal` with the classical value coerced, so it also says that the left side is finite. -/
theorem data_processing_label {L d : Type} [Fintype L] [Fintype d] [DecidableEq d]
    (ρ : L → Matrix d d ℂ) (hρ : ∀ x, WildeQIT.IsDensityOperator (ρ x)) (q p : L → ℝ)
    (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hsupp : ∀ x, p x = 0 → q x = 0) (n : ℕ) :
    relativeEntropy (ensembleState q ρ n) (ensembleState p ρ n) ≤ ((labelRelEntropy q p : ℝ) : EReal) := by sorry

end PrettyGoodShadow
