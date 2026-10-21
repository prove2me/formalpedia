-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_topological_extension_compatibility
-- name    : QAlgorithms.Papers.Independent.Next46.P06.topological_extension_compatibility
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:46:02.49948+00:00
-- url     : https://prove2.me/theorems/28f048c1-52d1-4816-9bbd-b097dcc8787a
-- title:
--   Corollary 9.2
-- statement:
--   Let $F$ be a unital subalgebra of a unital complex algebra $G$, and $\Phi:F\to\mathcal C(X)$ a calculus on a complex Banach space. Let a subalgebra $E$ be an algebraic core, and let $E\subseteq E'\subseteq G$ be a subalgebra. Suppose $\Phi|_E$ takes values in an operator subalgebra $A$ and is jointly closable for algebraic convergence relations $(\tau_1,\tau_2)$ on $(E',A)$. Construct $E^\tau$, its bounded topological extension, and then its canonical algebraic extension $\Phi^\tau$ to $G^\tau=\langle E^\tau,G,\Phi^\tau|_{E^\tau}\rangle$. Then
--
--   $$ f\in F\cap G^\tau\ \Longrightarrow\ \Phi^\tau(f)\subseteq\Phi(f).$$
--
--   Equality holds if $\Phi^\tau(f)$ is bounded, and in particular on $F\cap E^\tau$. If $f\in F$ and $Z(E^\tau)\cap[f]_E$ is an anchor, then $f\in G^\tau$ and equality holds. Thus $\Phi^\tau$ extends $\Phi$ if $E\subseteq Z(E^\tau)$. If $E$ is commutative and $\tau_1$ is Hausdorff, then $E^\tau$ is commutative and the same extension conclusion holds.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 23, Corollary 9.2

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P06

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter

open scoped Topology

namespace QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore)

universe u v w

variable {F G : Type*} [Ring F] [Algebra ℂ F] [Ring G] [Algebra ℂ G]

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Corollary 9.2, PDF p.23, including the final paragraph: graph inclusion,
bounded equality, the center criterion, and compatibility when E commutes and
tau1 is Hausdorff. E^tau and its canonical extension are constructed by the
previous definitions, rather than supplied as unrelated maps. -/
theorem topological_extension_compatibility [CompleteSpace X] {I : Type*}
    (S : Subalgebra ℂ F) (Ep : Set F) (hEp : SubalgebraSet Ep)
    (Phi : F → Graph X) (hPhi : CalculusOn Phi (S : Set F))
    (E : Set F) (hE : SubalgebraSet E) (hcore : AlgebraicCoreOn Phi E (S : Set F))
    (hEEp : E ⊆ Ep) (A : Set (X →L[ℂ] X)) (hA : SubalgebraSet A)
    (himage : ∀ e ∈ E, boundedValue (Phi e) ∈ A)
    (tau1 : (I → F) → F → Prop)
    (tau2 : (I → (X →L[ℂ] X)) → (X →L[ℂ] X) → Prop)
    (htau1 : AlgebraicConvergenceOn tau1 Ep)
    (htau2 : AlgebraicConvergenceOn tau2 A)
    (hclosable : JointClosable (fun f => boundedValue (Phi f)) E tau1 tau2) :
    let Et := topologicalDomain (fun f => boundedValue (Phi f)) E A tau1 tau2
    let rt := topologicalValue (fun f => boundedValue (Phi f)) E A tau1 tau2
    let Gt := maximalAnchored rt Et
    let Pt := canonicalAlgebraicExtension rt Et
    (∀ f ∈ (S : Set F) ∩ Gt, Pt f ⊆ Phi f ∧ (Bounded (Pt f) → Pt f = Phi f)) ∧
    (∀ f ∈ (S : Set F) ∩ Et, Pt f = Phi f) ∧
    (∀ f ∈ (S : Set F), AnchorSet Phi (setCenter Et ∩ symbolBracket E f) →
      f ∈ Gt ∧ Pt f = Phi f) ∧
    (E ⊆ setCenter Et → ∀ f ∈ (S : Set F), f ∈ Gt ∧ Pt f = Phi f) ∧
    (CommutativeSet E → HausdorffConvergence tau1 →
      CommutativeSet Et ∧ ∀ f ∈ (S : Set F), f ∈ Gt ∧ Pt f = Phi f) := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
