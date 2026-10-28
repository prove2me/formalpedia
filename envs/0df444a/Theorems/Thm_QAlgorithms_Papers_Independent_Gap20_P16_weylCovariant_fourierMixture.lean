-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P16_weylCovariant_fourierMixture
-- name    : QAlgorithms.Papers.Independent.Gap20.P16.weylCovariant_fourierMixture
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:38:39.298997+00:00
-- url     : https://prove2.me/theorems/a851008f-7ddf-4510-a722-87a83ad9a379
-- title:
--   Fourier probability law and corrected random-unitary formula
-- statement:
--   Let $H$ be a finite abelian group and $\widehat H$ its full unit-circle character group. Let $d\ge1$, and let $U_\alpha,V_\beta$ be unitary representations on $\mathbb C^d$ with $V_\beta U_\alpha=\beta(\alpha)U_\alpha V_\beta$. Set $W_{(\alpha,\beta)}=U_\alpha V_\beta$ and assume irreducibility. Every CPTP map $\Phi$ satisfying $\Phi(W_z^*XW_z)=W_z^*\Phi(X)W_z$ for all $z,X$ admits a probability law $p$ on $\widehat H\times H$ such that
--
--   $$
--   \begin{gathered}
--   \Phi(W_{(\alpha,\beta)})=\varphi(\alpha,\beta)W_{(\alpha,\beta)},\qquad
--   \varphi(\alpha,\beta)=\sum_{(x,y)\in\widehat H\times H}p_{x,y}x(\alpha)\beta(y),\\
--   \Phi(X)=\sum_{(x,y)\in\widehat H\times H}p_{x,y}W_{(-y,x)}XW_{(-y,x)}^*
--   \quad\text{for every matrix }X.
--   \end{gathered}
--   $$
--
--   The weights are nonnegative and sum to one. The sum expresses the channel as an average of unitary conjugations. **Source correction:** the PDF prints the adjoints in the opposite positions in (11); the displayed formula reverses them to agree with the positive Fourier phase in (10) and the conjugation law (7). Round-one moderation independently verified this correction against the rendered PDF and a hand calculation; the edited theorem needs fresh readbacks.
--
--   Conversely, for every nonnegative law $p$ on $\widehat H\times H$ with total mass one, the displayed mixture defines a completely positive trace-preserving Weyl-covariant map and satisfies the displayed eigenoperator identity with characteristic function $\varphi=\widehat p$. The probability law is arbitrary in this converse, rather than only the law obtained from a given channel.
-- source:
--   Remarks on the classical capacity of quantum channel, arXiv:quant-ph/0212025v1, PDF p. 4, §1, (10)–(11), corrected

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P16

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P16

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat Unitary)

/-- PDF p.4, (10)--(11): every Weyl-covariant channel has a Fourier
probability law and the associated random-unitary representation on ALL
operators. SOURCE CORRECTION: printed W_J^* X W_J is changed to W_J X W_J^*
to agree with (7),(10) and their stated proof. For H=Z/3, a mass at (x=1,y=0)
gives V U V^*=omega U, whereas the printed adjoints give omega^(-1) U.
The converse states that EVERY probability law gives a Weyl-covariant CPTP
map with the same positive-phase symbol. The adjoint correction was independently
audited in MODERATION-r1.md; the edited statement requires fresh readbacks. -/
theorem weylCovariant_fourierMixture
    {d : ℕ} (hd : 0 < d) {H : Type*} [AddCommGroup H] [Fintype H]
    [Fintype (CharacterGroup H)] (W : FiniteAbelianWeylSystem H d) (hirr : QAlgorithms.Papers.Independent.Support21.P09.Irreducible (fun z => (finiteAbelianWeylOperator W z : Mat d)))
    (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi)
    (hcov : WeylCovariant W Phi) :
    (∃ p : CharacterGroup H × H → ℝ, (∀ t, 0 ≤ p t) ∧ (∑ t, p t = 1) ∧
      (∀ z, Phi (finiteAbelianWeylOperator W z : Mat d) = fourierCharacteristic p z • (finiteAbelianWeylOperator W z : Mat d)) ∧
      ∀ X : Mat d, Phi X = fourierMixture W p X) ∧
    (∀ p : CharacterGroup H × H → ℝ, (∀ t, 0 ≤ p t) → (∑ t, p t = 1) →
      IsChannel (fourierMixture W p) ∧ WeylCovariant W (fourierMixture W p) ∧
      ∀ z, fourierMixture W p (finiteAbelianWeylOperator W z : Mat d) =
        fourierCharacteristic p z • (finiteAbelianWeylOperator W z : Mat d)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P16

end
