-- Prove2me | Theorems.Thm_WeightedCongestionBR_lemma_4
-- name    : WeightedCongestionBR.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:17:35.444266+00:00
-- url     : https://prove2.me/theorems/ee8f99f5-1442-485e-9dcc-32f769030f83
-- title:
--   Lemma 4 — $w\,c_e(x+w)\le\phi_e(x+w)-\phi_e(x)\le\alpha\,w\,c_e(x+w)$
-- statement:
--   Let $d$ be a positive integer and $c_e\in\mathfrak P_d$ the cost of a resource $e$, with potential $\phi_e$ from (5) and $\alpha=d+1$ from (6). For any $x\ge0$ and $w\ge1$,
--
--   $$
--   w\cdot c_e(x+w)\le\phi_e(x+w)-\phi_e(x)\le\alpha\cdot w\cdot c_e(x+w).
--   $$
--
--   It makes $\Phi$ an $\alpha$-approximate potential and underlies Lemmas 5, 6, 8 and 10. The condition $w\ge1$ cannot be dropped ($d=1$, $c(t)=t$, $x=0$, $w=1/2$).
--
--   Differences from the source:
--   - encoding: any resource e of a game of degree d → any polynomial P ∈ 𝔓_d with potential phiPoly P; reason: the cost of a resource of a degree-d game is a polynomial of 𝔓_d, and every such polynomial is a possible cost
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Lemma 4, p.11

import Mathlib
import Definitions.Def_WeightedCongestionBR_IsPd
import Definitions.Def_WeightedCongestionBR_phiPoly
import Definitions.Def_WeightedCongestionBR_alphaC
set_option autoImplicit false
open scoped NNReal

namespace WeightedCongestionBR

/-- **Lemma 4** (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, p.11). For any resource `e`, `x ≥ 0` and `w ≥ 1`:
`w · c_e(x + w) ≤ φ_e(x + w) − φ_e(x) ≤ α · w · c_e(x + w)`, with `φ_e` from (5) and `α = d + 1` from (6).

**Formalization Note** A resource of a game of degree `d` is represented by its cost polynomial
`P ∈ 𝔓_d`; every such polynomial is the cost of some resource. -/
theorem lemma_4 (d : ℕ) (hd : 1 ≤ d) (P : Polynomial ℝ) (hP : IsPd d P) (x w : ℝ) (hx : 0 ≤ x)
    (hw : 1 ≤ w) :
    w * P.eval (x + w) ≤ phiPoly P (x + w) - phiPoly P x ∧
      phiPoly P (x + w) - phiPoly P x ≤ alphaC d * w * P.eval (x + w) := by sorry

end WeightedCongestionBR
