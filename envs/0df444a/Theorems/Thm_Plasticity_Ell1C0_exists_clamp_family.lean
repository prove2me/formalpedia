-- Prove2me | Theorems.Thm_Plasticity_Ell1C0_exists_clamp_family
-- name    : Plasticity.Ell1C0.exists_clamp_family
-- status  : Proved
-- author  : @scanstone
-- created : 2026-11-18T19:24:54.3192+00:00
-- url     : https://prove2.me/theorems/d0b650d8-b0a9-436b-8385-72871f65f070
-- title:
--   Prescribing the images of the unit vectors of $\ell_1(J)$ in $c_0(J\times\mathbb N)$ by a finite modification of a fixed injective map
-- statement:
--   Let $J$ be a set, $I=J\times\mathbb N$, $e_j$ the unit vectors of $\ell_1(J)$ and $H(x)_{(j,k)}=2^{-(k+2)}x_j$.
--   There is a family of maps $G_y\colon B_{\ell_1(J)}\to B_{c_0(I)}$, indexed by label families $y=(y_j)_{j\in J}$ in $B_{c_0(I)}$, such that for all $y$:
--   (1) $G_y$ is nonexpansive; (2) $G_y(e_j)=y_j$; (3) $G_y(x)$ depends only on the labels $y_j$ with $x_j>\|x\|_1/4$; (4) if no $x_j$ exceeds $\|x\|_1/4$ then $G_y(x)=H(x)$; (5) if $x$ is not a unit vector $e_j$, then $G_y(x)$ and $H(x)$ differ at only finitely many coordinates.
-- source:
--   Proof draft 'Three constructions of nonplastic Banach unit balls' (ChatGPT Pro, OpenAI, 18 November 2026), Lemma 2.1 and Construction A (prescribing images, finite dependence)

import Definitions.Def_Plasticity_SeqSpace

namespace Plasticity
theorem Ell1C0.exists_clamp_family (J : Type*) [DecidableEq J] :
    ∃ G : (J → Metric.closedBall (0 : c0 (J × ℕ)) 1) →
        Metric.closedBall (0 : lp (fun _ : J => ℝ) 1) 1 → Metric.closedBall (0 : c0 (J × ℕ)) 1,
      (∀ y, LipschitzWith 1 (G y)) ∧
      (∀ y j (x : Metric.closedBall (0 : lp (fun _ : J => ℝ) 1) 1),
        (x : lp (fun _ : J => ℝ) 1) = lp.single 1 j 1 → G y x = y j) ∧
      (∀ y y' (x : Metric.closedBall (0 : lp (fun _ : J => ℝ) 1) 1),
        (∀ j, ‖(x : lp (fun _ : J => ℝ) 1)‖ / 4 < (x : lp (fun _ : J => ℝ) 1) j → y j = y' j) →
        G y x = G y' x) ∧
      (∀ y (x : Metric.closedBall (0 : lp (fun _ : J => ℝ) 1) 1),
        (∀ j, (x : lp (fun _ : J => ℝ) 1) j ≤ ‖(x : lp (fun _ : J => ℝ) 1)‖ / 4) →
        ∀ i : J × ℕ, ((G y x : c0 (J × ℕ)) : Linf (J × ℕ)) i
            = (2 : ℝ) ^ (-((i.2 : ℤ) + 2)) * (x : lp (fun _ : J => ℝ) 1) i.1) ∧
      (∀ y (x : Metric.closedBall (0 : lp (fun _ : J => ℝ) 1) 1),
        (∀ j, (x : lp (fun _ : J => ℝ) 1) ≠ lp.single 1 j 1) →
        {i : J × ℕ | ((G y x : c0 (J × ℕ)) : Linf (J × ℕ)) i
            ≠ (2 : ℝ) ^ (-((i.2 : ℤ) + 2)) * (x : lp (fun _ : J => ℝ) 1) i.1}.Finite) := by sorry
end Plasticity
