-- Prove2me | Theorems.Thm_PlanarQueue_Planar_complete_queue_number
-- name    : PlanarQueue.Planar.complete_queue_number
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:24:29.259074+00:00
-- url     : https://prove2.me/theorems/704d6ddf-4439-4d76-bab5-b943de70afa6
-- title:
--   The complete graph on ℓ vertices has queue-number ⌊ℓ/2⌋
-- statement:
--   For every nonnegative integer $\ell$, the complete graph $K_\ell$ has queue-number exactly $\lfloor\ell/2\rfloor$:
--
--   $$
--   \operatorname{qn}(K_\ell)=\left\lfloor\frac{\ell}{2}\right\rfloor.
--   $$
--
--   This gives the queues needed for edges within a single part and layer in Lemma 8.
--
--   **Formalization Note** Exactness is stated as existence of a layout with $\lfloor\ell/2\rfloor$ queues and nonexistence with any smaller number. The cases $\ell=0,1$ admit zero queues.
-- source:
--   Dujmović, Joret, Micek, Morin, Ueckerdt, Wood, Planar graphs have bounded queue-number, arXiv:1904.04791v5, p. 11, proof of Lemma 8, citing Heath–Rosenberg [69]

import Mathlib
import Definitions.Def_PlanarQueue_Planar_Setting

namespace PlanarQueue.Planar

/-- The complete graph on ℓ vertices has queue-number exactly ⌊ℓ/2⌋. -/
theorem complete_queue_number (ℓ : ℕ) :
    HasQueueLayout (⊤ : SimpleGraph (Fin ℓ)) (ℓ / 2) ∧
      ∀ k : ℕ, k < ℓ / 2 → ¬ HasQueueLayout (⊤ : SimpleGraph (Fin ℓ)) k := by sorry

end PlanarQueue.Planar
