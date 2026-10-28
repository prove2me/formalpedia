-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P43_alternative_relative_decomposition
-- name    : QAlgorithms.Papers.Independent.Support50.P43.alternative_relative_decomposition
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:33:47.926708+00:00
-- url     : https://prove2.me/theorems/e231e8ad-7eab-43ef-be09-11408cf1805a
-- title:
--   Decomposition into cut relative entropies minus CQMI
-- statement:
--   All entropies are von Neumann entropies in bits, with zero eigenvalues contributing zero. For a normalized positive semidefinite state $\rho$ on $n\ge2$ nonzero finite-dimensional local complex spaces, write $S(T)=S(\rho_T)$ for the marginal entropy, $[n]=\{1,\ldots,n\}$, and $\bar i=[n]\setminus\{i\}$. Define
--   $$
--   I(\rho)=\sum_{i=1}^n S(\bar i)-(n-1)S([n]),\qquad I_x(\rho)=\sum_{i=1}^n S(\{i\})-S([n]).
--   $$
--
--   Write $D(\rho\|\sigma)$ for genuine Umegaki relative entropy in bits, with value $+\infty$ unless the support of $\rho$ is contained in that of $\sigma$. Each product reference below is regrouped on the original joint Hilbert space. Then
--   $$I(\rho)=\sum_{i=1}^n D(\rho\|\rho_i\otimes\rho_{\bar i})-D(\rho\|\bigotimes_{i=1}^n\rho_i).$$
--
--   Every relative entropy occurring here is finite for a density input, so the subtraction is well-defined. This supplies a second representation independent of the rejected replicated-space identity.
-- source:
--   Multiparty Quantum Mutual Information: An alternative definition, arXiv:1504.07176v2, PDF p. 3, Equation (13), middle line

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P43

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- These accepted register types are definitionally the required finite tensor bases.

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis)

open QAlgorithms.Papers.Independent.Information100.P21 (ghzKet)

/-- Equation (13), middle line, PDF p.3: sum of cut relative entropies minus
conventional information. All reference products live on the original joint basis.
The relative entropies here are finite for every density input. -/
theorem alternative_relative_decomposition {n : ℕ} (hn : 2 ≤ n)
    {D : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hrho : IsDensityMatrix rho) :
    (alternativeOn rho Finset.univ : EReal) =
      (∑ i, (QAlgorithms.Papers.Independent.Information100.P60.relativeBits
        rho (cutProduct rho {i}) : EReal)) -
        (QAlgorithms.Papers.Independent.Information100.P60.relativeBits
          rho (singletonProduct rho) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Support50.P43

end
