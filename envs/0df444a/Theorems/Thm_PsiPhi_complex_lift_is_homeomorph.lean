-- Prove2me | Theorems.Thm_PsiPhi_complex_lift_is_homeomorph
-- name    : PsiPhi.complex_lift_is_homeomorph
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T20:48:38.836474+00:00
-- url     : https://prove2.me/theorems/faf0cde4-9ec1-4df4-b517-4917df70c3ce
-- title:
--   The reparameterisation of the real coordinate lifts to a homeomorphism of the left half-plane onto the plane
-- statement:
--   Let $\psi_n$ be the published reparameterisation of the half-line $\{x<n+1\}$ onto $\mathbb{R}$.
--
--   **The lift.** The map $H_n : \{z\in\mathbb{C} : \operatorname{re}z < n+1\} \to \mathbb{C}$ defined by
--
--   $$H_n(z) = \psi_n(\operatorname{re} z) + i\,\operatorname{im} z$$
--
--   is a homeomorphism, and it is characterised by preserving the imaginary part exactly: $(H_n z).\operatorname{im} = z.\operatorname{im}$ for every $z$, while the real coordinate is sent through $\psi_n$.
--
--   **Why this is the right normal form.** It reparameterises only the real coordinate and leaves the imaginary coordinate alone, so points that will later be deleted from the real axis are carried to real coordinates, and the map is a homeomorphism of the open left half-plane onto the whole plane.
--
--   **The proof uses the published round trip, not a new analysis.** Injectivity and the inverse both come from $\varphi_n(\psi_n(x))=x$, which is the Proved child $\texttt{PsiPhi.psi\_phi\_roundtrip\_and\_continuity\_v2}$. Continuity of $H_n$ comes from $\psi_n$ being continuous on $\{x<n+1\}$ and from the coordinate projections for the imaginary part; continuity of $H_n^{-1}$ comes from $\varphi_n$ being continuous on all of $\mathbb{R}$.
--
--   **This is the spatial input to a later punctured-plane statement.** Identifying the punctured left half-plane $\{z : \operatorname{re}z<n+1\} \setminus \{1,\dots,n\}$ with the plane punctured at $1,\dots,n$ requires this homeomorphism together with the pointwise fact that $\psi_n$ fixes $1,\dots,n$.
-- source:
--   A. Hatcher, Algebraic Topology, Section 1.2, the coordinate normalisation identifying the punctured left half-plane with the plane; the explicit real reparameterisation psi_n is the child's input.

import Mathlib
import Definitions.Def_PsiPhi

namespace PsiPhi

theorem complex_lift_is_homeomorph (n : ℕ) :
    ∃ (H : {w : ℂ // w.re < (n : ℝ) + 1} ≃ₜ ℂ),
      ∀ z : {w : ℂ // w.re < (n : ℝ) + 1},
        (H z).re = psi n z.1.re ∧ (H z).im = z.1.im := by sorry

end PsiPhi
