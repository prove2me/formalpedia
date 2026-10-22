-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P16_weylCovariance_iff_positiveDefinite
-- name    : QAlgorithms.Papers.Independent.Gap20.P16.weylCovariance_iff_positiveDefinite
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:37:39.330178+00:00
-- url     : https://prove2.me/theorems/39ccf1ae-41f4-4dbd-bebb-41355a94df2c
-- title:
--   Weyl-covariant channels are normalized positive-definite diagonal multipliers
-- statement:
--   Let $H$ be a finite abelian group, let $\widehat H$ be its full unit-circle character group, and let $G=H\times\widehat H$. On $\mathbb C^d$ with $d\ge1$, let $U$ and $V$ be unitary representations of $H$ and $\widehat H$ satisfying $V_\beta U_\alpha=\beta(\alpha)U_\alpha V_\beta$. Put $W_{(\alpha,\beta)}=U_\alpha V_\beta$, and assume this family is irreducible. For every complex-linear matrix map $\Phi$,
--
--   $$
--   \begin{aligned}
--   &\Phi\text{ is CPTP and }\Phi(W_z^*XW_z)=W_z^*\Phi(X)W_z\quad(\forall z,X)\\
--   &\quad\Longleftrightarrow\quad
--   \exists\varphi:G\to\mathbb C:\ \varphi(0)=1,\quad\varphi\text{ is positive definite},\quad
--   \Phi(W_z)=\varphi(z)W_z\quad(\forall z).
--   \end{aligned}
--   $$
--
--   Positive definiteness means that $[\varphi(z_j-z_k)]_{j,k}$ is positive semidefinite for every finite list of group elements, allowing repetitions. CPTP means completely positive and trace preserving. This characterizes the channels through a scalar function and includes the normalized converse construction.
--
--   Conversely, for every normalized positive-definite symbol $\varphi$, construct the map on all matrices by
--
--   $$\Phi_{\varphi}(X)=\sum_{z\in G}\frac{\operatorname{Tr}(W_z^*X)}{d}\varphi(z)W_z.$$
--
--   Then $\Phi_{\varphi}$ is completely positive, trace preserving and Weyl-covariant, and $\Phi_{\varphi}(W_z)=\varphi(z)W_z$ for every $z$. The trace formula is the linear extension of the prescribed values on the Weyl operator basis.
-- source:
--   Remarks on the classical capacity of quantum channel, arXiv:quant-ph/0212025v1, PDF p. 3, §1, (8)–(9)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P16

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P16

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat Unitary)

/-- PDF pp.3--4, (8)--(9): linear maps are Weyl-covariant channels iff
they are diagonal Weyl multipliers with normalized positive-definite symbol.
Normalization phi(0)=1 is forced by trace preservation and is essential in
the converse. No positivity assumption is imposed on the forward implication.
The second clause retains the source's construction for EVERY normalized
positive-definite symbol, using the explicit trace expansion above. -/
theorem weylCovariance_iff_positiveDefinite
    {d : ℕ} (hd : 0 < d) {H : Type*} [AddCommGroup H] [Fintype H]
    [Fintype (CharacterGroup H)]
    (W : FiniteAbelianWeylSystem H d) (hirr : QAlgorithms.Papers.Independent.Support21.P09.Irreducible (fun z => (finiteAbelianWeylOperator W z : Mat d)))
    (Phi : Mat d →ₗ[ℂ] Mat d) :
    ((IsChannel Phi ∧ WeylCovariant W Phi) ↔
      ∃ phi : H × CharacterGroup H → ℂ, phi 0 = 1 ∧ PositiveDefinite phi ∧
        ∀ z, Phi (finiteAbelianWeylOperator W z : Mat d) = phi z • (finiteAbelianWeylOperator W z : Mat d)) ∧
    (∀ phi : H × CharacterGroup H → ℂ, phi 0 = 1 → PositiveDefinite phi →
      IsChannel (finiteAbelianWeylMultiplier W phi) ∧
      WeylCovariant W (finiteAbelianWeylMultiplier W phi) ∧
      ∀ z, finiteAbelianWeylMultiplier W phi (finiteAbelianWeylOperator W z : Mat d) =
        phi z • (finiteAbelianWeylOperator W z : Mat d)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P16

end
