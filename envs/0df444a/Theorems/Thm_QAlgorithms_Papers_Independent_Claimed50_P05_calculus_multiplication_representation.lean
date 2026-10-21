-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_multiplication_representation
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_multiplication_representation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:10:57.917981+00:00
-- url     : https://prove2.me/theorems/c9bc996c-875d-4d97-8652-161117fa47ec
-- title:
--   Theorem 4.7
-- statement:
--   Let $k$ be $\mathbb R$ or $\mathbb C$, let $H$ be a Hilbert space, and let $(X,\Sigma)$ be a measurable space. Write $M(X)$ for the finite $k$-valued measurable functions with pointwise equality, and $M_b(X)$ for its bounded functions. Let $\Phi:M(X)\to C(H)$ satisfy axioms MFC1–MFC5, where $C(H)$ consists of closed functional linear graphs. All operator equalities include equality of domains; an overline on an operator denotes graph closure.
--
--   There exist a semifinite measure space $(\Omega,\mathcal F,\mu)$, a unitary $U:H\to L^2(\mu;k)$, and an injective unital $k$-linear star homomorphism $T:M(X)\to M(\Omega)$ such that
--
--   $$U\Phi(f)U^{-1}=M_{Tf}\qquad(f\in M(X)).$$
--
--   The map $T$ preserves pointwise convergence of sequences, without a boundedness assumption. The equation uses transported graphs and includes their domains.
--
--   This represents the entire calculus by multiplication, with the unitary orientation supplied by the source proof.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 18, Theorem 4.7

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ENNReal InnerProductSpace

namespace QAlgorithms.Papers.Independent.Claimed50.P05

universe u v w

variable {k : Type*} [RCLike k]

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace k H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace k K] [CompleteSpace K]

/-- Theorem 4.7, PDF pp.18–19. Transport is oriented as in the correctly typed proof on p.19.
Source correction (independently audited in moderation round 1).
Printed: Theorem 4.7 gives U:H to L2 but displays Phi(f)=U M_(Tf) U^(-1).
Changed: Keep U:H to L2 and state U Phi(f) U^(-1)=M_(Tf), exactly the equation in the proof on p.19.
Why: The printed conjugation is ill-typed for the specified direction of U. The proof supplies the uniquely typed orientation. Pointwise injectivity of T, semifiniteness and sequential pointwise continuity are retained; a zero-measure copy of the base can preserve injectivity even for H={0}.
-/
theorem calculus_multiplication_representation {B : Type u} [MeasurableSpace B]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace k E]
    (F : Symbol B k → Relation E) (hF : Calculus F) :
    ∃ (Omega : Type (max u v)) (m : MeasurableSpace Omega) (mu : @Measure Omega m)
      (U : E ≃ₗᵢ[k] Lp k 2 mu) (T : Symbol B k → @Symbol Omega k m _),
      Semifinite mu ∧ SymbolHom T ∧ Function.Injective T ∧
      (∀ f, unitaryGraphTransport U (F f) = multiplication mu (T f)) ∧
      (∀ fn f, Pointwise fn f → Pointwise (fun n => T (fn n)) (T f)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
