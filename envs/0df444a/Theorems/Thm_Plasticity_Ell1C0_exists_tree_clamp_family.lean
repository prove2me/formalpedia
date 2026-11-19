-- Prove2me | Theorems.Thm_Plasticity_Ell1C0_exists_tree_clamp_family
-- name    : Plasticity.Ell1C0.exists_tree_clamp_family
-- status  : Proved
-- author  : @scanstone
-- created : 2026-11-18T20:09:20.741601+00:00
-- url     : https://prove2.me/theorems/fa66d0b1-4039-4aaf-8594-7c7441c38c28
-- title:
--   Prescribing images on closed code sets in the blocks of $\ell_1(\mathbb N\times\mathbb N)$ by a finite modification of a fixed injective map
-- statement:
--   Let $J=\mathbb N\times\mathbb N$ with blocks $J_n=\{n\}\times\mathbb N$, $I=J\times\mathbb N$, $H(x)_{(j,k)}=2^{-(k+2)}x_j$, and $D(x)=\{n:\|x|_{J_n}\|_1>\|x\|_1/4\}$.
--   There is a rule $G$ assigning to each family of sets $E_n\subseteq\ell_1(J)$ and each label map $\lambda\colon\ell_1(J)\to B_{c_0(I)}$ a map $G_{E,\lambda}\colon B_{\ell_1(J)}\to B_{c_0(I)}$ such that, whenever each $E_n$ is a closed set of nonnegative unit vectors supported in $J_n$ and $\|\lambda e-\lambda e'\|\le\|e-e'\|_1/4$ for $e,e'\in E_n$ with $\|e-e'\|_1<2$:
--   (1) $G_{E,\lambda}$ is nonexpansive; (2) $G_{E,\lambda}=\lambda$ on each $E_n$; (3) $G_{E,\lambda}(x)$ depends only on $E_n$ and $\lambda|_{E_n}$ for $n\in D(x)$ (for every other family $E',\lambda'$); (4) $G_{E,\lambda}(x)=H(x)$ if $D(x)=\varnothing$; (5) $G_{E,\lambda}(x)-H(x)$ is finitely supported for $x\notin\bigcup_nE_n$.
-- source:
--   Proof draft 'Three constructions of nonplastic Banach unit balls' (ChatGPT Pro, OpenAI, 18 November 2026), Construction B (finite modification on a tree); the quarter condition replaces the tree structure

import Definitions.Def_Plasticity_SeqSpace

namespace Plasticity
theorem Ell1C0.exists_tree_clamp_family :
    ∃ G : (ℕ → Set (lp (fun _ : ℕ × ℕ => ℝ) 1)) →
        (lp (fun _ : ℕ × ℕ => ℝ) 1 → Metric.closedBall (0 : c0 ((ℕ × ℕ) × ℕ)) 1) →
        Metric.closedBall (0 : lp (fun _ : ℕ × ℕ => ℝ) 1) 1 →
        Metric.closedBall (0 : c0 ((ℕ × ℕ) × ℕ)) 1,
      ∀ (E : ℕ → Set (lp (fun _ : ℕ × ℕ => ℝ) 1))
        (lab : lp (fun _ : ℕ × ℕ => ℝ) 1 → Metric.closedBall (0 : c0 ((ℕ × ℕ) × ℕ)) 1),
        (∀ n, IsClosed (E n)) →
        (∀ n, ∀ e ∈ E n, ‖e‖ = 1 ∧ ∀ j, 0 ≤ e j ∧ (j.1 ≠ n → e j = 0)) →
        (∀ n, ∀ e ∈ E n, ∀ e' ∈ E n, ‖e - e'‖ < 2 → dist (lab e) (lab e') ≤ ‖e - e'‖ / 4) →
        LipschitzWith 1 (G E lab) ∧
        (∀ n (x : Metric.closedBall (0 : lp (fun _ : ℕ × ℕ => ℝ) 1) 1),
          (x : lp (fun _ : ℕ × ℕ => ℝ) 1) ∈ E n → G E lab x = lab x) ∧
        (∀ (E' : ℕ → Set (lp (fun _ : ℕ × ℕ => ℝ) 1))
          (lab' : lp (fun _ : ℕ × ℕ => ℝ) 1 → Metric.closedBall (0 : c0 ((ℕ × ℕ) × ℕ)) 1)
          (x : Metric.closedBall (0 : lp (fun _ : ℕ × ℕ => ℝ) 1) 1),
          (∀ n, ‖(x : lp (fun _ : ℕ × ℕ => ℝ) 1)‖ / 4 <
              ∑' m, |(x : lp (fun _ : ℕ × ℕ => ℝ) 1) (n, m)| →
            E' n = E n ∧ ∀ e ∈ E n, lab' e = lab e) →
          G E' lab' x = G E lab x) ∧
        (∀ (x : Metric.closedBall (0 : lp (fun _ : ℕ × ℕ => ℝ) 1) 1),
          (∀ n, ∑' m, |(x : lp (fun _ : ℕ × ℕ => ℝ) 1) (n, m)| ≤
              ‖(x : lp (fun _ : ℕ × ℕ => ℝ) 1)‖ / 4) →
          ∀ i : (ℕ × ℕ) × ℕ, ((G E lab x : c0 ((ℕ × ℕ) × ℕ)) : Linf ((ℕ × ℕ) × ℕ)) i
            = (2 : ℝ) ^ (-((i.2 : ℤ) + 2)) * (x : lp (fun _ : ℕ × ℕ => ℝ) 1) i.1) ∧
        (∀ (x : Metric.closedBall (0 : lp (fun _ : ℕ × ℕ => ℝ) 1) 1),
          (∀ n, (x : lp (fun _ : ℕ × ℕ => ℝ) 1) ∉ E n) →
          {i : (ℕ × ℕ) × ℕ | ((G E lab x : c0 ((ℕ × ℕ) × ℕ)) : Linf ((ℕ × ℕ) × ℕ)) i
            ≠ (2 : ℝ) ^ (-((i.2 : ℤ) + 2)) * (x : lp (fun _ : ℕ × ℕ => ℝ) 1) i.1}.Finite) := by sorry
end Plasticity
