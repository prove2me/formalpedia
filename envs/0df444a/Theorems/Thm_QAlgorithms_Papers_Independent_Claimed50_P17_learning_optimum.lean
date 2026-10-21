-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P17_learning_optimum
-- name    : QAlgorithms.Papers.Independent.Claimed50.P17.learning_optimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:01:27.055762+00:00
-- url     : https://prove2.me/theorems/9c37df36-8b5a-44db-a0c1-e4ab7c33f932
-- title:
--   Attained optimal measurement-learning fidelity and alpha maximization
-- statement:
--   Let $d\ge2$, and let $A,B,C,D$ be copies of $\mathbb C^d$ with a fixed basis. The unknown device is used once and implements $E_i(U)=U|i\rangle\langle i|U^\dagger$, returning only its classical label on $D$. Strategy data are independent of $U$. A cloning instrument is an array $R_{ij}\succeq0$ with $\sum_{ij}R_{ij}=I_D\otimes S_{ABC}$, $S\succeq0$, and $\operatorname{Tr}_C S=I_{AB}$. A learning instrument instead satisfies $\sum_{ij}R_{ij}=I_{ABD}\otimes\rho_C$, $\rho\succeq0$, $\operatorname{Tr}\rho=1$. All tensors are transported to wire order $((A,B),C),D$.
--
--   Write $G_{ij}^R(U)=[R_{ij}*E(U)]^T$ for the replica obtained with the unnormalized Choi convention and fixed-basis transpose. Its Haar score is
--   $$F(R)=\frac1{d^2}\int\sum_{ij}\operatorname{Re}\operatorname{Tr}\bigl[G_{ij}^R(U)(E_i(U)\otimes E_j(U))\bigr]\,dU.$$
--   The measure is normalized Haar on $SU(d)$; averaging over $U(d)$ gives precisely the same labeled-measurement law because scalar phases cancel.
--
--   Use the scaled blocks $s_\ell^\nu=(n_\ell/d)r_\ell^\nu$ in the concrete Schur representation, where $n_\ell$ counts the triples in equality-pattern class $\ell$; the five classes are $xxx,xxy,xyx,xyy,xyz$, with $xyz$ and gamma absent at $d=2$. Put
--   $$a_\star=\frac{d+1}{18d(d-1)},\qquad s_{xxx}^\alpha=\operatorname{diag}(1/d-2a_\star,0),$$
--   $$s_{xyx}^\alpha=\begin{pmatrix}a_\star&\sqrt{a_\star/(2d)}\\\sqrt{a_\star/(2d)}&1/(2d)\end{pmatrix},\quad s_{xyy}^\alpha=\sigma_zs_{xyx}^\alpha\sigma_z.$$
--   The other alpha blocks vanish. The beta scalar is $1/d$ only at $xxy$; for $d\ge3$ the gamma scalar is $1/d$ only at $xyz$. All other blocks vanish. For any positive array with the stated sector and class supports, operational learning feasibility is equivalent to the block normalization: the alpha sum is $I_2/d$ and each present scalar-sector sum is $1/d$. The displayed blocks satisfy these constraints.
--
--   The resulting operational learning instrument $R_\star$ attains the maximum over all feasible learning instruments:
--   $$F(R)\le F(R_\star)=\begin{cases}7/12,&d=2,\\(9d^2+16d-17)/[6d^2(d^2-1)],&d\ge3.\end{cases}$$
--   For $0\le a\le1/(2d)$ define the scalar alpha bound
--   $$f_d(a)=\frac1d\left[\frac{5d-3}{2d(d^2-1)}-\frac{3a}{d+1}+2\sqrt{\frac{a}{2d(d^2-1)}}\right].$$
--   Then $a_\star$ lies in this interval and
--   $$f_d(a)\le f_d(a_\star)=\frac{4(2d-1)}{3d^2(d^2-1)}.$$
--   The displayed instrument has alpha score $f_d(a_\star)$, beta score $1/d^2$, and gamma score $1/(2d^2)$ when gamma is present. Its optimal score is asymptotic to $3/(2d^2)$, in the sense that their ratio tends to one as $d\to\infty$.
--
--   This gives the attained learning optimum through actual operational blocks, including the swap partner implicit in Eq.(44). The full replica formula after Eq.(78) is stated separately for this same instrument when $d\ge3$.
-- source:
--   Cloning of a quantum measurement, arXiv:1103.5709v2, PDF p. 9, §VI, Eqs.(70)–(78): optimal learning fidelity and block maximization

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P17

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

/-- arXiv:1103.5709v2 PDF p.9, Eqs.(70)-(78): operational learning
maximum, attained through actual Schur blocks, with the alpha scalar maximization
and the d=2 exception. The later replica formula is stated separately for d>=3. -/
theorem learning_optimum (d : ℕ) (hd : 2 ≤ d) :
    let a := learningParameter d
    let b := learningBlocks d a
    (∀ c : BlockArray, BlockShape d c →
      (IsReplicationStrategy .learning (expandBlocks d c) ↔ c ∈ learningBlockSet d)) ∧
    b ∈ learningBlockSet d ∧ IsReplicationStrategy .learning (expandBlocks d b) ∧
    haarReplicationScore (expandBlocks d b) = learningValue d ∧
    (∀ R : ReplicationChoiArray d, IsReplicationStrategy .learning R → haarReplicationScore R ≤ learningValue d) ∧
    a ∈ Set.Icc 0 (1/(2*(d : ℝ))) ∧
    learningAlphaBound d a = 4*(2*(d : ℝ)-1)/(3*(d : ℝ)^2*((d : ℝ)^2-1)) ∧
    (∀ t ∈ Set.Icc 0 (1/(2*(d : ℝ))), learningAlphaBound d t ≤ learningAlphaBound d a) ∧
    sectorScore d b 0 = learningAlphaBound d a ∧
    sectorScore d b 1 = 1/(d : ℝ)^2 ∧
    sectorScore d b 2 = (if d = 2 then 0 else 1/(2*(d : ℝ)^2)) ∧
    Filter.Tendsto (fun n : ℕ => learningValue n / (3/(2*(n : ℝ)^2)))
      Filter.atTop (nhds 1) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P17

end
