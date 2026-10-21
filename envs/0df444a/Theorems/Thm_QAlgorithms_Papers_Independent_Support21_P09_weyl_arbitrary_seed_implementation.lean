-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P09_weyl_arbitrary_seed_implementation
-- name    : QAlgorithms.Papers.Independent.Support21.P09.weyl_arbitrary_seed_implementation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:50:02.435994+00:00
-- url     : https://prove2.me/theorems/af49a01c-cb0e-4c85-8a8e-f3fb8062ea27
-- title:
--   Arbitrary-seed Weyl implementation and conditional efficiency
-- statement:
--   Let $k\ge2$, $m=2^k$, and $v\in\mathbb C^m$ satisfy $\sum_r|v_r|^2=1/m$. Use the shift $S$ and clock $T$ of the preceding result and define the labeled columns $M_{:,j,l}=T^lS^jv$. They form a rank-one POVM whose effects equal the physical effects with unit seed $\psi=\sqrt m\,v$. Set
--
--   $$
--   Z=\bigoplus_{j=0}^{m-1}T^{-j},\qquad W=Z^\dagger(F_m^\dagger\otimes F_m),\qquad a_v=\sqrt m\,v^T F_m^\dagger.
--   $$
--
--   The matrix $W$ is unitary. For the ordinary group $G_m=\langle S,T\rangle$, there exists an ordinary monomial unitary representation $R$ with $gM=MR(g)$, $R(T)=I_m\otimes S$, $R(S)=S\otimes T^\dagger$, and
--
--   $$
--   WR(g)W^\dagger=I_m\otimes g,\qquad MW^\dagger=a_v\otimes I_m.
--   $$
--
--   There exists $A\in U(m)$ with first row $a_v$. Every such $A$ gives
--
--   $$
--   D=(F_m\otimes F_m^\dagger)Z(A^\dagger\otimes I_m),
--   $$
--
--   whose adjoint has $M$ as its first $m$ rows. Applying $D$ to $|0\rangle\langle0|\otimes\rho$ and measuring computationally gives exactly the original POVM probabilities for every density matrix $\rho$. One polynomial, independent of $v$, bounds exact elementary circuit sizes for each of $F_m\otimes F_m^\dagger$ and $Z$ on $2k$ qubits. Thus an efficient synthesis of $A$ gives an efficient implementation; arbitrary $A$ is not claimed to have efficient synthesis.
-- source:
--   Implementation of group-covariant POVMs by orthogonal measurements, arXiv:quant-ph/0407054v1, PDF p. 19, §6.3: arbitrary-seed Weyl-Heisenberg implementation

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P09

open scoped BigOperators ComplexConjugate

open QAlgorithms.Papers.Independent.Frontier18.P17 (clock)

/-- PDF pp.18–20, §6.3: arbitrary-seed completion and Figure 2 factorization.
The intertwiner row has m entries (p.19's n is a typo). Clock-then-positiveShift columns follow
p.18; the physical shift-then-clock effects agree up to column phases. No unconditional
polynomial synthesis of arbitrary A is claimed. -/
theorem weyl_arbitrary_seed_implementation :
    (∀ k : ℕ, ∀ hk : 2 ≤ k, ∀ v : Fin (2 ^ k) → ℂ,
      (∑ r, ‖v r‖ ^ 2) = (1 : ℝ) / ((2 ^ k : ℕ) : ℝ) →
      let m := 2 ^ k
      let M := weylColumns m v
      RankOnePOVM M ∧
      (∀ o, columnEffect M o = phaseSpaceEffect m
        ((Real.sqrt m : ℂ) • WithLp.toLp 2 v) o) ∧
      weylW m ∈ Matrix.unitaryGroup (Fin m × Fin m) ℂ ∧
      (∃ R : Rep (weylGroup m) (Fin m × Fin m),
        UnitaryRep R ∧ (∀ g, Monomial (R g)) ∧
        MatrixIntertwines (naturalAction (weylGroup m)) R M ∧
        (∀ g, weylW m * R g * (weylW m).conjTranspose =
          Matrix.kronecker (1 : Matrix (Fin m) (Fin m) ℂ)
            (naturalAction (weylGroup m) g)) ∧
        (∀ g, naturalAction (weylGroup m) g = clock m →
          R g = Matrix.kronecker (1 : Matrix (Fin m) (Fin m) ℂ) (positiveShift m)) ∧
        (∀ g, naturalAction (weylGroup m) g = positiveShift m →
          R g = Matrix.kronecker (positiveShift m) (clock m).conjTranspose)) ∧
      (M * (weylW m).conjTranspose =
        fun r p => weylRow m v p.1 * (1 : Matrix (Fin m) (Fin m) ℂ) r p.2) ∧
      (∃ A : Matrix (Fin m) (Fin m) ℂ,
        A ∈ Matrix.unitaryGroup (Fin m) ℂ ∧ ∀ j, A 0 j = weylRow m v j) ∧
      (∀ A : Matrix (Fin m) (Fin m) ℂ,
        A ∈ Matrix.unitaryGroup (Fin m) ℂ → (∀ j, A 0 j = weylRow m v j) →
        (∀ r j, (weylD m A).conjTranspose (0, r) j = M r j) ∧
        ImplementsPOVM M (weylD m A) (fun r => (0, r)))) ∧
    (∃ p : Polynomial ℕ, ∀ k : ℕ, 2 ≤ k →
      ∃ fourierCirc clockCirc : Circuit elementaryGates (k + k),
        fourierCirc.size ≤ p.eval k ∧ clockCirc.size ≤ p.eval k ∧
        fourierCirc.unitary =
          (Matrix.kronecker (qftMatrix (2 ^ k)) ((qftMatrix (2 ^ k)).conjTranspose)).submatrix
            (registerIndex k k) (registerIndex k k) ∧
        clockCirc.unitary = (weylZ (2 ^ k)).submatrix
          (registerIndex k k) (registerIndex k k)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P09

end
