-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P09_algorithm_six_completion
-- name    : QAlgorithms.Papers.Independent.Support21.P09.algorithm_six_completion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:46:03.893732+00:00
-- url     : https://prove2.me/theorems/6db9a75c-656a-4194-978d-0ee8542379ce
-- title:
--   Correctness and freedom of Algorithm 6
-- statement:
--   Let $G$ be finite and $n=d+c$ with $d>0,c\ge0$. Let $M\in\mathbb C^{d\times n}$ define a POVM of distinct nonzero rank-one effects, with ordinary unitary symmetries $\phi:G\to U(d)$ and monomial $R:G\to U(n)$ satisfying $\phi M=MR$. Let $U\in U(d)$ and $W\in U(n)$ completely reduce the two representations into pairwise inequivalent irreducible matrix models with multiplicities. There exist a completely reduced unitary complementary representation $\chi$ and a unitary $\widetilde C$ whose first $d$ rows equal $C=UMW^\dagger$, such that
--
--   $$
--   [(U\phi(g)U^\dagger)\oplus\chi(g)]\widetilde C=\widetilde C[WR(g)W^\dagger].
--   $$
--
--   For every complementary representation and unitary completion satisfying these conditions, and every $V\in U(c)$, set
--
--   $$
--   B=(U^\dagger\oplus V^\dagger)\widetilde C W.
--   $$
--
--   The first $d$ rows of $B$ equal $M$, $B^\dagger$ exactly implements all labeled effect probabilities for every density matrix embedded in the first coordinates, and
--
--   $$
--   [\phi(g)\oplus(V^\dagger\chi(g)V)]B=BR(g).
--   $$
--
--   This includes existence of the completion and the freedom to choose its remaining rows and $V$. A change of $V$ conjugates the complementary symmetry. The case $c=0$ is included.
-- source:
--   Implementation of group-covariant POVMs by orthogonal measurements, arXiv:quant-ph/0407054v1, PDF p. 11, Algorithm 6: correctness and freedom of the completion construction

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P09

open scoped BigOperators ComplexConjugate

open QAlgorithms.Papers.Independent.Frontier18.P17 (clock)

/-- PDF pp.9–11, Algorithm 6: existence of the intertwining completion is a conclusion.
Every allowed Ctilde and V give an implementation. Changing V conjugates the complement
by V^dagger; it does not preserve a fixed complementary representation. The p.11 "rows"
is corrected to columns, consistently with pp.4–5. -/
theorem algorithm_six_completion
    {G : Type*} [Group G] [Fintype G] {d c : ℕ} (hd : 0 < d)
    (phi : Rep G (Fin d)) (R : Rep G (Fin (d + c)))
    (hphi : UnitaryRep phi) (hR : UnitaryRep R) (hmon : ∀ g, Monomial (R g))
    (M : Matrix (Fin d) (Fin (d + c)) ℂ) (hM : RankOnePOVM M)
    (hdist : Function.Injective (columnEffect M)) (hsym : MatrixIntertwines phi R M)
    (U : Matrix (Fin d) (Fin d) ℂ) (W : Matrix (Fin (d + c)) (Fin (d + c)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin (d + c)) ℂ)
    (hredU : Reduced (fun g => U * phi g * U.conjTranspose))
    (hredW : Reduced (fun g => W * R g * W.conjTranspose)) :
    (∃ chi : Rep G (Fin c), UnitaryRep chi ∧ Reduced chi ∧
      ∃ C : Matrix (Fin (d + c)) (Fin (d + c)) ℂ,
        C ∈ Matrix.unitaryGroup (Fin (d + c)) ℂ ∧
        (∀ i j, C (Fin.castAdd c i) j = (U * M * W.conjTranspose) i j) ∧
        (∀ g, sumBlock (U * phi g * U.conjTranspose) (chi g) * C =
          C * (W * R g * W.conjTranspose))) ∧
    (∀ chi : Rep G (Fin c), UnitaryRep chi →
      ∀ C : Matrix (Fin (d + c)) (Fin (d + c)) ℂ,
      C ∈ Matrix.unitaryGroup (Fin (d + c)) ℂ →
      (∀ i j, C (Fin.castAdd c i) j = (U * M * W.conjTranspose) i j) →
      (∀ g, sumBlock (U * phi g * U.conjTranspose) (chi g) * C =
        C * (W * R g * W.conjTranspose)) →
      ∀ V : Matrix (Fin c) (Fin c) ℂ, V ∈ Matrix.unitaryGroup (Fin c) ℂ →
      let B := sumBlock U.conjTranspose V.conjTranspose * C * W
      (∀ i j, B (Fin.castAdd c i) j = M i j) ∧
      ImplementsPOVM M B.conjTranspose (Fin.castAdd c) ∧
      (∀ g, sumBlock (phi g) (V.conjTranspose * chi g * V) * B = B * R g)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P09

end
