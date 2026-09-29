-- Prove2me | Theorems.Thm_VectorCalculus_energy_conservation
-- name    : VectorCalculus.energy_conservation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T00:20:38.926301+00:00
-- url     : https://prove2.me/theorems/0e282c94-66fb-4a04-ba7b-1e741f359d32
-- title:
--   Conservation of energy: $K + V$ is constant for $m\ddot{\mathbf{x}} = -\nabla V$
-- statement:
--   Let $V$ be a continuously differentiable potential on $\mathbb R^n$ and let $\mathbf x(t)$ be a twice continuously differentiable trajectory obeying Newton's second law with the conservative force $\mathbf F = -\nabla V$,
--
--   $$m\ddot{\mathbf x}(t) = -\nabla V\bigl(\mathbf x(t)\bigr).$$
--
--   Then the total energy is conserved: there is a constant $E$ with
--
--   $$\tfrac12 m\,|\dot{\mathbf x}(t)|^2 + V\bigl(\mathbf x(t)\bigr) = E \qquad\text{for all } t .$$
-- source:
--   David Tong, Vector Calculus, University of Cambridge Part IA Mathematical Tripos lecture notes, http://www.damtp.cam.ac.uk/user/tong/vc.html, §1.3.3 (p. 24), equation (1.18) and the conclusion $K(t) + V(t) = \text{constant}$

import Definitions.Def_VectorCalculus_grad

namespace VectorCalculus

theorem energy_conservation {n : ℕ} (m : ℝ) (V : (Fin n → ℝ) → ℝ) (hV : ContDiff ℝ 1 V)
    (x : ℝ → (Fin n → ℝ)) (hx : ContDiff ℝ 2 x)
    (hnewton : ∀ (t : ℝ) (i : Fin n),
      m * deriv (fun s => deriv (fun u => x u i) s) t = -grad V (x t) i) :
    ∃ E : ℝ, ∀ t : ℝ,
      (1 / 2) * m * (∑ i, (deriv (fun s => x s i) t) ^ 2) + V (x t) = E := by sorry

end VectorCalculus
