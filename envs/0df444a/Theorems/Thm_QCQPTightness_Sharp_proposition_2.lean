-- Prove2me | Theorems.Thm_QCQPTightness_Sharp_proposition_2
-- name    : QCQPTightness.Sharp.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:23:30.441199+00:00
-- url     : https://prove2.me/theorems/73a47975-df97-41c5-9731-9deb1b26d27b
-- title:
--   Proposition 2, pp. 21–22 — the multiplicity bound k ≥ aff dim{b(γ) : γ ∈ ℱ} + 1 of Theorems 1 and 2 cannot be lowered to k ≥ aff dim{b(γ) : γ ∈ ℱ}
-- statement:
--   For any positive integers $n$ and $k$ there exists a QCQP in $N=nk$ variables with $m=k+1$ constraints such that
--
--   1. Assumptions 1 and 3 are satisfied,
--   2. the quadratic eigenvalue multiplicity of the QCQP is $k$,
--   3. for every semidefinite face $\mathcal F$ of $\Gamma$,
--   $$
--   k\ \ge\ \operatorname{aff\,dim}\big(\{b(\gamma) : \gamma\in\mathcal F\}\big),
--   $$
--   4. but $\mathrm{Opt}\ne\mathrm{Opt}_{\mathrm{SDP}}$, and hence $\operatorname{conv}(\mathcal D)\ne\mathcal D_{\mathrm{SDP}}$.
--
--   Theorems 1 and 2 of the paper guarantee $\operatorname{conv}(\mathcal D)=\mathcal D_{\mathrm{SDP}}$ and $\mathrm{Opt}=\mathrm{Opt}_{\mathrm{SDP}}$ under Assumptions 1 and 3 when $k\ge\operatorname{aff\,dim}\{b(\gamma):\gamma\in\mathcal F\}+1$ for every semidefinite face. This proposition shows that the "+1" cannot be removed.
--
--   **Formalization Note** The QCQP is existentially quantified over `QCQP (n * k) (k + 1)`, so $N=nk$ and $m=k+1$ are fixed as on the page. "The multiplicity is $k$" is `IsQuadEigMult k` ($k$ is the largest admissible integer). Faces are nonempty. Both conclusions of the last bullet are stated.
-- source:
--   arXiv:1911.09195v3, Proposition 2, pp. 21–22

import Mathlib
import Definitions.Def_QCQPTightness_Sharp_QCQP
import Definitions.Def_QCQPTightness_Sharp_Faces
import Definitions.Def_QCQPTightness_Sharp_Mult

namespace QCQPTightness.Sharp

/-- Proposition 2 (arXiv:1911.09195v3, pp. 21–22): for all positive integers `n`, `k` there is a
QCQP in `N = nk` variables with `m = k + 1` constraints satisfying Assumptions 1 and 3, with
quadratic eigenvalue multiplicity `k`, with `k ≥ aff dim{b(γ) : γ ∈ ℱ}` for every semidefinite
face `ℱ` of `Γ`, but with `Opt ≠ Opt_SDP` (and hence `conv(𝒟) ≠ 𝒟_SDP`). -/
theorem proposition_2 : ∀ n k : ℕ, 0 < n → 0 < k →
    ∃ P : QCQP (n * k) (k + 1),
      P.Assumption1 ∧ P.Assumption3 ∧ P.IsQuadEigMult k ∧
      (∀ F : Set (Fin (k + 1) → ℝ), P.IsSemidefiniteFace F → affdim (P.bγ '' F) ≤ k) ∧
      P.Opt ≠ P.OptSDP ∧ convexHull ℝ P.D ≠ P.DSDP := by sorry

end QCQPTightness.Sharp
