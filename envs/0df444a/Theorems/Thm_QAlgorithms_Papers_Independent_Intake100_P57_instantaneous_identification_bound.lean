-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P57_instantaneous_identification_bound
-- name    : QAlgorithms.Papers.Independent.Intake100.P57.instantaneous_identification_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:59:24.186491+00:00
-- url     : https://prove2.me/theorems/0df51f66-5626-43d4-9737-3763a83d8b98
-- title:
--   Entanglement-dimension bound for instantaneous state identification
-- statement:
--   Let $d\ge1$ be a prime power and fix $d+1$ pairwise mutually unbiased orthonormal bases $\{|e_x^a\rangle\}_{x=1}^d$, indexed by $a=0,\ldots,d$, of $\mathbb C^d$. Alice's input register has basis $|a\rangle$ and dimension $d+1$; Bob's input has dimension $d$. Choose $x$ uniformly from $1,\ldots,d$ and supply
--
--   $$
--   \rho^x_{AB}=\frac1{d+1}\sum_{a=0}^d|a\rangle\langle a|\otimes|e_x^a\rangle\langle e_x^a|.
--   $$
--
--   Let $\eta_{A'B'}$ be any density matrix on arbitrary finite nonempty local registers of dimensions $l,r$, independent of $x$. Alice and Bob apply any fixed local POVMs on $AA'$ and $BB'$ without communication and compute a guess $g(\alpha,\beta)$ in their common causal future. Their finite outcome alphabets have no prescribed size bound. The probability of correctly guessing $x$, averaged over the specified ensemble, satisfies
--
--   $$
--   p_{\mathrm{succ}}\le\frac{2r}{\sqrt d}.
--   $$
--
--   This bounds every instantaneous measurement, even with an arbitrary mixed resource and unrestricted local computation. The resource charged is $\dim B'=r$.
--
--   **Formalization Note** Prime powers are written $p^k$ with prime $p$ and natural $k$; the harmless $d=1$ case is retained.
-- source:
--   Simplified instantaneous non-local quantum computation with applications to position-based cryptography, arXiv:1101.1065v3, PDF p. 10, IV.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P57

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P57

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- P34 uses half the channel distance. Every occurrence below is multiplied by two.

open QAlgorithms.Papers.Independent.Information100.P34 (diamondDistance)

open QAlgorithms.Papers.Independent.Dependency50.P07 (ensembleMean)

/-- Theorem IV.1, PDF p.10, with section assumptions on p.9.
The prime-power exponent is natural, so the trivial d=1 case remains meaningful. -/
theorem instantaneous_identification_bound (d l r : ℕ) (hd : 0 < d)
    (hprime : ∃ p k : ℕ, Nat.Prime p ∧ d = p^k) (hl : 0 < l) (hr : 0 < r)
    (U : Fin (d+1) → Matrix.unitaryGroup (Fin d) ℂ) (hU : IsMUB d U)
    (eta : Matrix (Fin l × Fin r) (Fin l × Fin r) ℂ) (heta : IsDensityMatrix eta)
    (s : InstantMeasurement (d+1) d l r d) :
    mubSuccess U s eta ≤ 2 * (r : ℝ) / Real.sqrt (d : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P57

end
