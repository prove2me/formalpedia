-- Prove2me | Theorems.Thm_RobustUncLP_Ellipsoidal_uncSet_eq_image_PFeas
-- name    : RobustUncLP.Ellipsoidal.uncSet_eq_image_PFeas
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:29:28.3885+00:00
-- url     : https://prove2.me/theorems/b9a49184-3194-452a-9419-60a31baf04ab
-- title:
--   Appendix, p. 15 — 𝒰 is the set of values of Π₀(u⁰) on the feasible set of (P_i[x])
-- statement:
--   Let $\mathcal U = \bigcap_{\ell=0}^k U(\Pi_\ell, Q_\ell)$ be given by the data of (15), and let $F$ be the feasible set of $(P_i[x])$, i.e. the tuples $(u^0,\dots,u^k)$ with $\Pi_\ell(u^\ell) = \Pi_0(u^0)$ and $\|Q_\ell u^\ell\| \le 1$ for all $\ell$. Then
--   $$\mathcal U = \{\Pi_0(u^0) \mid (u^0, \dots, u^k) \in F\}.$$
--
--   This identity rewrites "for all $A \in \mathcal U$" as a minimization over $F$, which is the first step of the proof of Theorem 3.1. No hypothesis on the data is needed.
-- source:
--   Ben-Tal & Nemirovski, Robust solutions of uncertain linear programs, Oper. Res. Lett. 25 (1999); authors' manuscript, Appendix, p. 15, sentence after (P_i[x]) ("Indeed, …")

import Mathlib
import Definitions.Def_RobustUncLP_Ellipsoidal_Setting
import Definitions.Def_RobustUncLP_Ellipsoidal_SystemC

namespace RobustUncLP.Ellipsoidal

open Matrix EllipsoidalData

/-- Appendix, p. 15 ("Indeed, …"): `𝒰` is exactly the set of values of `Π_0(u⁰)` on the feasible
set of `(P_i[x])`. -/
theorem uncSet_eq_image_PFeas {m n k : ℕ} (D : EllipsoidalData m n k) :
    D.uncSet = (fun u => D.Pi 0 (u 0)) '' PFeas D := by sorry

end RobustUncLP.Ellipsoidal
