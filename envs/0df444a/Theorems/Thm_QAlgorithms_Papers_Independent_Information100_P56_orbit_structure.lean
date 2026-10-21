-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P56_orbit_structure
-- name    : QAlgorithms.Papers.Independent.Information100.P56.orbit_structure
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:13:35.393063+00:00
-- url     : https://prove2.me/theorems/9c81223d-ceaf-4ad3-ada9-9189790184ef
-- title:
--   Proposition II.2: orbit structure and redundant input labels
-- statement:
--   Let the input alphabet be finite and nonempty, and let Bob and Eve have nonzero finite-dimensional output spaces. Each channel output is a positive semidefinite matrix of trace one. Entropies and information rates use natural logarithms, with $0\log0=0$. Suppose a finite group $G$ acts transitively on the input alphabet $X$, with simultaneous covariance under possibly projective representations $U_B,U_E$. Choose $x_0\in X$ and let $H$ be its stabilizer. Then $X$ is equivariantly identified with the left cosets $G/H$, and, for both receivers,
--
--   $$W_R(g\cdot x_0)=U_R(g)W_R(x_0)U_R(g)^\dagger,\qquad U_R(h)W_R(x_0)U_R(h)^\dagger=W_R(x_0)\quad(h\in H).$$
--
--   Conversely, any pair of $H$-invariant density seeds defines such a channel. For every $n\ge1$, lifting any finite auxiliary/input law from $X^n$ to $G^n$, or pushing it back along $g\mapsto g\cdot x_0$, preserves both induced cq ensembles. Hence redundant group labels leave every $C^{(n)}$ unchanged. This permits the regular-action description without assuming the original action is free.
-- source:
--   From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels, arXiv:2610.03580v1, PDF p. 4, Proposition II.2: orbit structure and redundant input labels

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Proposition II.2, p.4: left stabilizer cosets, both orbit identities and the converse,
plus exact preservation of all finite-use private information and both cq ensembles
under lifting and pushing any finite auxiliary/input law. -/
theorem orbit_structure
    {G X B E : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq X]
    [MulAction G X] [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype E] [DecidableEq E] [Nonempty E]
    (x0 : X) (htrans : ∀ x : X, ∃ g : G, g • x0 = x)
    (UB : ProjectiveRep G B) (UE : ProjectiveRep G E)
    (WB : X → Matrix B B ℂ) (WE : X → Matrix E E ℂ) (hW : IsWiretap WB WE)
    (hcovB : ∀ g x, WB (g • x) =
      (UB.unitary g : Matrix B B ℂ) * WB x * (UB.unitary g : Matrix B B ℂ)ᴴ)
    (hcovE : ∀ g x, WE (g • x) =
      (UE.unitary g : Matrix E E ℂ) * WE x * (UE.unitary g : Matrix E E ℂ)ᴴ) :
    (∃ e : Quotient (actionRelation x0) ≃ X,
      ∀ g : G, e (Quotient.mk (actionRelation x0) g) = g • x0) ∧
    (∀ g h : G, (actionRelation x0).r g h ↔ (g⁻¹ * h) • x0 = x0) ∧
    (∀ g, WB (g • x0) = orbit UB (WB x0) g ∧ WE (g • x0) = orbit UE (WE x0) g) ∧
    (∀ h : G, h • x0 = x0 → orbit UB (WB x0) h = WB x0 ∧ orbit UE (WE x0) h = WE x0) ∧
    (∀ (sigmaB : Matrix B B ℂ) (sigmaE : Matrix E E ℂ),
      QAlgorithms.IsDensityMatrix sigmaB → QAlgorithms.IsDensityMatrix sigmaE →
      (∀ h : G, h • x0 = x0 → orbit UB sigmaB h = sigmaB ∧ orbit UE sigmaE h = sigmaE) →
      ∃ (YB : X → Matrix B B ℂ) (YE : X → Matrix E E ℂ), IsWiretap YB YE ∧
        (∀ g, YB (g • x0) = orbit UB sigmaB g ∧ YE (g • x0) = orbit UE sigmaE g) ∧
        (∀ g x, YB (g • x) = orbit UB (YB x) g ∧ YE (g • x) = orbit UE (YE x) g)) ∧
    (∀ n : ℕ, 1 ≤ n →
      blockPrivate n WB WE = blockPrivate n (fun g : G => WB (g • x0)) (fun g : G => WE (g • x0))) ∧
    (∀ (n k : ℕ), 1 ≤ n → 0 < k →
      let f : (Fin n → G) → (Fin n → X) := fun g i => g i • x0
      (∀ J : Fin k × (Fin n → X) → ℝ, IsLaw J →
        ∃ JG : Fin k × (Fin n → G) → ℝ, IsLaw JG ∧ pushJoint f JG = J) ∧
      (∀ JG : Fin k × (Fin n → G) → ℝ, IsLaw JG →
        IsLaw (pushJoint f JG) ∧ ∀ v : Fin k,
          cqBlock (productOutput n (fun g : G => WB (g • x0))) JG v =
            cqBlock (productOutput n WB) (pushJoint f JG) v ∧
          cqBlock (productOutput n (fun g : G => WE (g • x0))) JG v =
            cqBlock (productOutput n WE) (pushJoint f JG) v)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P56

end
