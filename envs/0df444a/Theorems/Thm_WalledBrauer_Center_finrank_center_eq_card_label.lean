-- Prove2me | Theorems.Thm_WalledBrauer_Center_finrank_center_eq_card_label
-- name    : WalledBrauer.Center.finrank_center_eq_card_label
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:08.896358+00:00
-- url     : https://prove2.me/theorems/da0845c0-7814-4bf5-9a4d-cce73c81053d
-- title:
--   Proof of Theorem 3.5 — if $B_{r,s}(\delta)$ is semisimple, $\dim Z(B_{r,s}(\delta))=|\dot\Lambda_{r,s}|$
-- statement:
--   If the walled Brauer algebra $B_{r,s}(\delta)$ is semisimple, then the dimension of its center equals the number of isomorphism classes of simple modules, which is the cardinality of $\dot\Lambda_{r,s}$:
--
--   $$
--   \dim_{\mathbb C} Z\bigl(B_{r,s}(\delta)\bigr)=\bigl|\dot\Lambda_{r,s}\bigr| .
--   $$
--
--   Here $\dot\Lambda_{r,s}=\Lambda_{r,s}$ unless $\delta=0$ and $r=s\ne0$, in which case the pair $(\varnothing,\varnothing)$ is removed. This is the dimension count in the proof of Theorem 3.5: it combines the Wedderburn–Artin theorem with the classification of the simple modules $D_{r,s}(\lambda)$, $\lambda\in\dot\Lambda_{r,s}$.
--
--   **Formalization Note** $\dot\Lambda_{r,s}$ is the published `Label r s δ` and the cardinality is `Nat.card` (the set is finite). The dimension is `Module.finrank ℂ` of `Subalgebra.center ℂ`, which is the same for the platform's product and its opposite.
-- source:
--   Jung–Kim, Supersymmetric polynomials and the center of the walled Brauer algebra, arXiv:1508.06469v2, p. 18, proof of Theorem 3.5 (with p. 7, [3, Theorem 2.7])

import Mathlib
import Definitions.Def_WalledBrauer_Center_Setting

namespace WalledBrauer.Center
open WalledBrauer.Blocks MvPolynomial

theorem finrank_center_eq_card_label (r s : ℕ) (δ : ℂ) (hss : IsSemisimpleRing (B r s δ)) :
    Module.finrank ℂ (Subalgebra.center ℂ (B r s δ)) = Nat.card (Label r s δ) := by sorry
end WalledBrauer.Center
