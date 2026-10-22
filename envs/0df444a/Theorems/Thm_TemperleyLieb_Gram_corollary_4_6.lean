-- Prove2me | Theorems.Thm_TemperleyLieb_Gram_corollary_4_6
-- name    : TemperleyLieb.Gram.corollary_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:48.119102+00:00
-- url     : https://prove2.me/theorems/9d974020-9189-4e0a-830a-a30f9e88ee7e
-- title:
--   Corollary 4.6, p. 18 — diagonal generator coefficients
-- statement:
--   Let $1\le k<n$, and let $s,t$ be tableaux of one shape with $t\triangleright s$. In the seminormal basis write $e_k(u,v)$ for the coefficient of $f_u$ in $f_ve_k$. If $e_k(s,t)\ne0$ and the shape of $t$ at stage $k$ is $(i,k-2i)$, then the two diagonal coefficients are
--
--   $$e_k(t,t)=\frac{p_{k-2i+1}}{p_{k-2i+2}},\qquad e_k(s,s)=\frac{p_{k-2i+3}}{p_{k-2i+2}}.$$
--
--   This gives the explicit coefficients used in the neighbouring seminormal norm ratio.
--
--   **Formalization Note** The coefficients are coordinates relative to an asserted seminormal basis of the computed cell module, and the theorem asserts the needed Murphy and JM data exist. The generator and tableau stage are restricted to the page's range.
-- source:
--   Enyang, Representations of Temperley–Lieb Algebras, arXiv:0710.3218v1, p. 18, Corollary 4.6, with Eq. (4.2) on p. 17

import Mathlib
import Definitions.Def_TemperleyLieb_Gram_Models

namespace TemperleyLieb.Gram
open QAlgorithms.Papers.Independent.Support21.P08

/-- Enyang, Corollary 4.6, p. 18: the two diagonal coefficients of `e_k`
for a neighbouring pair of seminormal tableaux. -/
theorem corollary_4_6 (n : ℕ) (hn : 2 ≤ n) :
    ∃ D : FDatum n, IsMurphyDatum F xF n D ∧
      ∃ J : JMFamily D (n + 1), IsPaperJMFamily n D J ∧
        ∀ f : Fin (n / 2 + 1),
          (∃ B : Module.Basis (Tab n f) F (Tab n f → F),
            ∀ u, B u = seminormalVector J f u) ∧
          ∀ (B : Module.Basis (Tab n f) F (Tab n f → F)),
            (∀ u, B u = seminormalVector J f u) →
            ∀ (k : ℕ) (hk0 : 1 ≤ k) (hkn : k < n)
              (s t : Tab n f) (hst : s < t)
              (hcoeff : B.repr (cellAct D f (seminormalVector J f t)
                (e F xF n k)) s ≠ 0)
              (i : ℕ) (hi : cups t k = i),
              B.repr (cellAct D f (seminormalVector J f t) (e F xF n k)) t =
                algebraMap R F (p (k - 2 * i + 1)) /
                  algebraMap R F (p (k - 2 * i + 2)) ∧
              B.repr (cellAct D f (seminormalVector J f s) (e F xF n k)) s =
                algebraMap R F (p (k - 2 * i + 3)) /
                  algebraMap R F (p (k - 2 * i + 2)) := by sorry

end TemperleyLieb.Gram
