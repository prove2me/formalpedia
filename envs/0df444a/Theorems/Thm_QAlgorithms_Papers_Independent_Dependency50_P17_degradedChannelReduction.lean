-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P17_degradedChannelReduction
-- name    : QAlgorithms.Papers.Independent.Dependency50.P17.degradedChannelReduction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:51:48.759816+00:00
-- url     : https://prove2.me/theorems/7e89be3c-c7d3-494d-b58e-9f059f35a838
-- title:
--   Affine encoding induces the sum-degraded product channel (38)
-- statement:
--   Let $F$ be a finite field of cardinality $p\ge2$, and let $W_{a,b}$ be the density-operator outputs of a memoryless cq-MAC on an arbitrary Hilbert register. Put $n=\ell+k$ and fix an invertible $F$-linear map $L:F^\ell\times F^k\to F^n$ and a shift $e\in F^n$. Define $g(m)=L(m,0)+e$. Alice encodes $a$ as $L(a,z)$, and Bob encodes $b$ as $L(b,-z)+e$, with a shared uniform seed $z$ hidden from the receiver. Their encoded sum is $g(a+b)$. If
--
--   $$
--   W^d_s=\frac1p\sum_{x\in F}W_{x,s-x},
--   $$
--
--   then for every $m\in F^\ell$,
--
--   $$
--   \frac{1}{p^{\ell+k}}\sum_{a\in F^\ell}\sum_{z\in F^k}
--   W^{\otimes n}_{L(a,z),\,L(m-a,-z)+e}
--   =(W^d)^{\otimes n}_{g(m)}.
--   $$
--
--   This is the actual average conditional on the uniformly distributed messages summing to $m$. Equality is stated in all orthonormal-basis coefficients and imposes no output-dimension cutoff. It supplies the simulation used in the computation-capacity lower bound.
--
--   **Formalization Note** The printed $q^{-n}$ in (38) is read as $p^{-n}$, the reciprocal of the number of summands.
-- source:
--   Computation-aided classical-quantum multiple access to boost network communication speeds, arXiv:2105.14505v1, PDF p. 13, Appendix C.A, (38)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P17

noncomputable section

open MeasureTheory

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Dependency50.P17

open QAlgorithms.Papers.Independent.Information100.P56 (productOutput)

/-- PDF pp.12–13, Appendix C.A, (38): the constructed affine encoders induce
exactly the degraded product channel, after averaging the hidden seed and the
uniform first message conditional on their sum. No channel-simulation hypothesis
is assumed. The fixed extension and affine shift precede every message and seed.
The printed q^(-n) is corrected to p^(-n)=|F|^(-n), as required by its summation set. -/
theorem degradedChannelReduction {F I : Type*} [Field F] [Fintype F]
    (W : CQMAC F I) {ell k : ℕ}
    (L : ((Fin ell → F) × (Fin k → F)) ≃ₗ[F] (Fin (ell + k) → F))
    (e : Fin (ell + k) → F) :
    (∀ (a b : Fin ell → F) (z : Fin k → F),
      aliceEncoder L z a + bobEncoder L e z b = sumEncoder L e (a + b)) ∧
    (∀ (m : Fin ell → F) (i j : Fin (ell + k) → I),
      conditionalSumOutput W L e m i j =
        degradedProduct W (sumEncoder L e m) i j) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P17

end
