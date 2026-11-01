-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P11_irreducibleProduct_converse
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P11.irreducibleProduct_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:47:35.070171+00:00
-- url     : https://prove2.me/theorems/0d27a361-74c6-4d51-b0fe-05d140b4a262
-- title:
--   Irreducible product-source rate-sum converse
-- statement:
--   Let $I$ be a finite label set, $p_i\ge0$ with $\sum_i p_i=1$, and let $|\phi_i\rangle\in\mathcal H_A$, $|\psi_i\rangle\in\mathcal H_B$ be unit vectors in finite-dimensional complex Hilbert spaces. Set $\mathcal E_{AB}=\{p_i,|\phi_i\rangle\otimes|\psi_i\rangle\}$. Assume that its positive-probability support admits no partition into two nonempty mutually orthogonal classes. Write $S(\mathcal E)$ for the base-two von Neumann entropy of its average density operator, and $\mathcal E_A,\mathcal E_B$ for its marginal ensembles. Every achievable real pair $(R_A,R_B)$ satisfies
--
--   $$
--   R_A+R_B\ge\frac{S(\mathcal E_A)+S(\mathcal E_B)+S(\mathcal E_{AB})}{2}.
--   $$
--
--   An achievable pair uses independent blind local CPTP encoders, one noiseless quantum link from each sender, and a joint CPTP decoder, without supplied shared entanglement or side messages. For every $\delta,\epsilon>0$, every sufficiently large positive integer blocklength $n$ admits positive compressed dimensions $d_A,d_B$ with $\log_2(d_A)/n\le R_A+\delta$, $\log_2(d_B)/n\le R_B+\delta$, and ensemble-average pure-input overlap with the reconstructed density operator at least $1-\epsilon$. Draws are independent and identically distributed; this is squared fidelity, without a purifying reference.
--
--   This is a necessary sum-rate constraint for globally irreducible product sources; it does not by itself characterize a complete rate region.
-- source:
--   On the distributed compression of quantum information, arXiv:quant-ph/0403042v3, PDF p. 6, Theorem III.3: irreducible product-source rate-sum converse

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P11

open MeasureTheory Filter

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Dependency50.P19 (both)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.6, Theorem III.3, (10): the rate-sum converse for globally irreducible
product sources. Irreducibility of the separate marginal ensembles is insufficient. -/
theorem irreducibleProduct_converse {I A B : Type*}
    [Fintype I] [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (htotal : ∑ i, p i = 1)
    (phi : I → EuclideanSpace ℂ A) (psi : I → EuclideanSpace ℂ B)
    (hphi : ∀ i, IsState (phi i)) (hpsi : ∀ i, IsState (psi i))
    (hirr : EnsembleIrreducible p (fun i => tensorVec (phi i) (psi i)))
    (ra rb : ℝ) (hach : FiniteAchievable p (fun i => tensorVec (phi i) (psi i)) ra rb) :
    (vnEntropy (sourceMean p phi) + vnEntropy (sourceMean p psi) +
      vnEntropy (sourceMean p (fun i => tensorVec (phi i) (psi i)))) / 2 ≤ ra + rb := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P11

end
