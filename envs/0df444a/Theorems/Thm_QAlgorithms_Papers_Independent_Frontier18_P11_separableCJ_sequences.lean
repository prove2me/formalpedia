-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P11_separableCJ_sequences
-- name    : QAlgorithms.Papers.Independent.Frontier18.P11.separableCJ_sequences
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:34:11.056562+00:00
-- url     : https://prove2.me/theorems/d42f0fb7-74fe-4dac-975d-77d3260faf97
-- title:
--   Sequences suffice on any dense linear subspace
-- statement:
--   Let $H_A,H_B$ be complex separable Hilbert spaces, and let $\Omega$ be a bounded positive operator on $H=H_B\otimes H_A$ with $\operatorname{Tr}_B\Omega=I_A$. Define $C_{BA}$ using the normalized finite separable sums from Definition 2. For every dense complex linear subspace $D\subseteq H$,
--
--   $$
--   \Omega\in C_{BA}\quad\Longleftrightarrow\quad
--   \exists(\Omega_n)_{n\ge0}\ \forall x,y\in D,\qquad
--   \lim_{n\to\infty}\langle x,\Omega_n y\rangle=\langle x,\Omega y\rangle,
--   $$
--
--   where every $\Omega_n$ is a finite sum $\sum_\alpha\rho_{n,\alpha}\otimes M_{n,\alpha}$, each $\rho_{n,\alpha}$ is an output density operator, and the positive input effects satisfy $\sum_\alpha M_{n,\alpha}=I_A$.
--
--   This gives a sequential description of the weak operator closure using matrix elements on a dense domain. The positivity and full marginal normalization of the proposed limit remain assumptions of the ambient class; weak convergence alone is not asserted to preserve the marginal.
-- source:
--   On the Choi-Jamiolkowski Correspondence in Infinite Dimensions, arXiv:1004.0196v3, PDF p. 6, Sequential description of separable CJ operators

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P11

noncomputable section

open scoped TensorProduct ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier18.P11

section Operators

variable {A B : Type*}

variable [NormedAddCommGroup A] [InnerProductSpace ℂ A]

variable [NormedAddCommGroup B] [InnerProductSpace ℂ B]

/-- Sequential consequence of Lemma 2, PDF p.6: within the normalized positive
ambient class, Definition 2 can use sequences converging weakly on any dense
linear subspace. No assertion that arbitrary weak limits preserve the marginal. -/
theorem separableCJ_sequences
    [CompleteSpace A] [CompleteSpace B]
    [SecondCountableTopology A] [SecondCountableTopology B]
    {I : Type*} [Countable I] (e : HilbertBasis I ℂ B)
    (O : JointHilbert A B →L[ℂ] JointHilbert A B)
    (hO : positiveOperator O) (hMarginal : inputMarginal e O)
    (D : Submodule ℂ (JointHilbert A B)) (hD : Dense (D : Set (JointHilbert A B))) :
    separableCJ e O ↔
      ∃ F : ℕ → (JointHilbert A B →L[ℂ] JointHilbert A B),
        (∀ n, finiteSeparableCJ e (F n)) ∧
        ∀ x ∈ D, ∀ y ∈ D,
          Filter.Tendsto (fun n => inner ℂ x (F n y)) Filter.atTop
            (nhds (inner ℂ x (O y))) := by sorry

end Operators

end QAlgorithms.Papers.Independent.Frontier18.P11

end
