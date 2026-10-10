-- Prove2me | Theorems.Thm_UhlenbeckGauge_norm_add_hodgeStar_sq
-- name    : UhlenbeckGauge.norm_add_hodgeStar_sq
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:23:53.532087+00:00
-- url     : https://prove2.me/theorems/63e321f5-9fdb-4035-8835-90d2ea8c52ef
-- title:
--   Lemma 3.1.2 — $|F\pm\star F|^2=2|F|^2\mp2\operatorname{tr}(F\wedge F)$
-- statement:
--   Let $F=(F_{\mu\nu})$ be an antisymmetric $\mathfrak{su}(n)$-valued two-form on $\mathbb R^4$ (at a point), $\star$ the Euclidean Hodge star, $|\cdot|^2$ the pointwise norm and $\operatorname{tr}(F\wedge F)$ the Chern–Weil density. Then
--   $$|F+\star F|^2=2|F|^2-2\operatorname{tr}(F\wedge F),\qquad |F-\star F|^2=2|F|^2+2\operatorname{tr}(F\wedge F).$$
--   In particular $\operatorname{tr}(F\wedge F)$ is real. This is the pointwise identity behind the decomposition of the Yang–Mills energy into an (anti-)self-duality defect and a topological term.
--
--   **Formalization Note** The printed statement in the notes has $\pm2\operatorname{tr}(F_A\wedge F_A)$; its proof on p. 32 arrives at $\mp2\operatorname{tr}(F_A\wedge F_A)$ using $B^*=-B$ on $\mathfrak{su}(n)$. The formalization follows the proof. The identity is stated in $\mathbb C$.
-- source:
--   K. Uhlenbeck, *Equations of Gauge Theory*, lecture notes by L. Fredrickson (Emil Grosswald Lectures, Temple University, February 7-9, 2012), Chapter 3, Section 3.1, pp. 29-32, Lemma 3.1.2 and its proof (p. 31-32)

import Definitions.Def_uhlenbeck_gauge_box_defs

open UhlenbeckGauge

namespace UhlenbeckGauge

theorem norm_add_hodgeStar_sq {n : ℕ} (F : TwoForm n) (hF : IsAntisymm F)
    (hsu : IsSuNValued F) :
    ((normSq (F + hodgeStar F) : ℝ) : ℂ) = 2 * (normSq F : ℂ) - 2 * trWedge F ∧
    ((normSq (F - hodgeStar F) : ℝ) : ℂ) = 2 * (normSq F : ℂ) + 2 * trWedge F := by sorry

end UhlenbeckGauge
