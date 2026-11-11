-- Prove2me | Theorems.Thm_QuadStatRE_Main_lemma_7_1
-- name    : QuadStatRE.Main.lemma_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:47:47.487513+00:00
-- url     : https://prove2.me/theorems/8cc3dea3-7914-4df3-ac7a-01b66978d128
-- title:
--   Lemma 7.1 — two-level estimate τ(A(A(W₀))) < 161/2000
-- statement:
--   Let $W_0$ be the equality-leakage family ($W_{0,s}$ reveals a uniform $V\in\mathbb F_2^3$ and the flag $\mathbf 1[V=s]$) and $W_2=\mathcal A(\mathcal A(W_0))$. Then
--   $$\tau(W_2)<\frac{161}{2000}=0.0805. \tag{7.1}$$
--
--   This is the only place where the specific structure of the basic gadget enters beyond affine symmetry: two RM steps bring the leakage close enough to the cubic regime that two applications of the scalar bound $B$ finish the job.
--
--   Differences from the source:
--
--   - encoding: W₂ = A(A(W₀)) → amp (amp W0) on (Fin 15 → Fin 15 → G × F₂); reason: the two-fold induced leakage of the equality leakage
--   - encoding: positions I = F₂⁴ ∖ {0} → Fin 15, position k the vector of binary digits of k + 1; reason: an enumeration of I; each nonzero vector occurs once
-- source:
--   Applebaum, Quadratic Statistical Randomized Encoding for All Functions, STOC 2027 submission (manuscript sha256 000cbf4e…), p. 33, Lemma 7.1, (7.1)

import Mathlib
import Definitions.Def_QuadStatRE_Main_ChiSquare
open QuadraticRE

namespace QuadStatRE.Main

/-- Lemma 7.1 (Two-level estimate), p. 33: for the equality-leakage family `W₀` and
`W₂ = A(A(W₀))`, `τ(W₂) < 161/2000 = 0.0805` (7.1). -/
theorem lemma_7_1 :
    tau (amp (amp W0)) < 161 / 2000 ∧ (161 / 2000 : ℝ) = 0.0805 := by sorry

end QuadStatRE.Main
