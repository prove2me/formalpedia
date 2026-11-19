-- Prove2me | Theorems.Thm_SymplecticBallPacking_compact_symplectomorphism_hamiltonian
-- name    : SymplecticBallPacking.compact_symplectomorphism_hamiltonian
-- status  : Open
-- author  : @LG
-- created : 2026-11-17T02:57:42.65756+00:00
-- url     : https://prove2.me/theorems/4bad9757-acd0-4c9b-bad0-c8092a465ed3
-- title:
--   Compactly supported symplectomorphisms of $\mathbb{R}^4$ are Hamiltonian
-- statement:
--   Every compactly supported symplectomorphism of $\mathbb R^4$ is Hamiltonian. Let $f:\mathbb C^2\to\mathbb C^2$ be a global symplectomorphism (smooth, a topological embedding, derivative preserving $\omega$ everywhere, bijective) with compact support, i.e. $f(x)=x$ outside some compact set. Then there exist a smooth Hamiltonian $H:\mathbb C^2\times\mathbb R\to\mathbb R$ with compact support and a Hamiltonian flow $\Phi$ on $[0,1]$ whose time-$1$ map is $f$:
--
--   $$\Phi_1=f.$$
--
--   This is the flux correspondence in the compactly supported setting: $H^1_c(\mathbb R^4;\mathbb R)=0$ forces the flux of any compactly supported symplectic isotopy to vanish, so it is homotopic to a Hamiltonian isotopy; and $\mathrm{Symp}_c(\mathbb R^4)$ is contractible (Gromov), so every compactly supported symplectomorphism lies in the identity component. It is the step that turns a symplectic packing into the Hamiltonian flow required by the goal.
--
--   **Formalization Note.** `HasCompactSupport` is taken on $\mathbb C^2\times\mathbb R$ (compact support in space and time); for the existential claim this is equivalent to spatial compact support uniform in $t\in[0,1]$, since $H$ may be cut off in time.
-- source:
--   McDuff–Salamon, Introduction to Symplectic Topology, 3rd ed., §10.2 (flux homomorphism; Ham = kernel of Flux); M. Gromov, Symp_c(ℝ⁴) contractible, see D. McDuff, A survey of the topological properties of symplectomorphism groups, Prop 1.1(i), https://arxiv.org/abs/math/0404340; M. M. R. Moreira, The flux homomorphism, Theorem 4, https://math.mit.edu/~miguel73/flux_hom.pdf.

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_SymplecticBallPacking
open scoped ContDiff

namespace SymplecticBallPacking
open OAI.HigherDimensionalBallPacking
open Set

theorem compact_symplectomorphism_hamiltonian (f : Phase 2 → Phase 2)
    (hf : IsSymplectomorphism f)
    (hcomp : ∃ K : Set (Phase 2), IsCompact K ∧ ∀ x ∉ K, f x = x) :
    ∃ (H : Phase 2 → ℝ → ℝ) (Φ : ℝ → Phase 2 → Phase 2),
      ContDiff ℝ ∞ (Function.uncurry H) ∧
      HasCompactSupport (Function.uncurry H) ∧
      IsHamiltonianFlow H Φ ∧ Φ 1 = f := by sorry

end SymplecticBallPacking
