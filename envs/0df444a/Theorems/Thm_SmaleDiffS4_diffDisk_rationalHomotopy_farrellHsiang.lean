-- Prove2me | Theorems.Thm_SmaleDiffS4_diffDisk_rationalHomotopy_farrellHsiang
-- name    : SmaleDiffS4.diffDisk_rationalHomotopy_farrellHsiang
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T12:47:22.546394+00:00
-- url     : https://prove2.me/theorems/4b6e9de1-a77e-4862-9ffb-922fc1e4cc76
-- title:
--   Farrell–Hsiang: $\pi_i\,\mathrm{Diff}(D^n)\otimes\mathbb Q$ in the stable range
-- statement:
--   Let $\mathrm{Diff}(D^n)$ be the group of diffeomorphisms of the $n$-ball that are the identity on the boundary, with the $C^\infty$ topology, based at the identity. For every $i\ge 2$ in the range
--
--   $$
--   i<\min\Bigl\{\frac{n-4}{3},\ \frac{n-7}{2}\Bigr\},$$
--
--   the rational homotopy groups are
--
--   $$
--   \pi_i\,\mathrm{Diff}(D^n)\otimes\mathbb Q\;\cong\;\begin{cases}\mathbb Q & \text{if } n \text{ is odd and } 4\mid i+1,\\ 0 & \text{otherwise.}\end{cases}$$
--
--   This is the Farrell–Hsiang computation quoted in the source; it shows that in high dimensions the homotopy of $\mathrm{Diff}(D^n)$ is far from trivial, in contrast with what was known in dimension $4$ when the problem was posed.
--
--   **Formalization Note** The index is written $i=j+2$, so only $i\ge2$ is covered: there $\pi_i$ is an abelian group in Mathlib, and $\pi_i\otimes\mathbb Q$ is `TensorProduct ℤ ℚ (Additive (π_i))`; "$\cong\mathbb Q$ / $\cong 0$" is expressed as $\mathbb Q$-dimension $1$ / $0$. The cases $i=0,1$ of the source's range ($0\le i$) are omitted, because Mathlib provides no group structure on $\pi_0$ and $\pi_1$ is only a (possibly non-abelian) group there. The parity condition "$n$ odd" is part of Farrell–Hsiang's theorem but is missing from the source page's (garbled) rendering of the formula.
-- source:
--   Open Problem Garden, 'What is the homotopy type of the group of diffeomorphisms of the 4-sphere?' (S. Smale; posted by rybu, 2009), http://www.openproblemgarden.org/op/what_is_the_homotopy_type_of_the_group_of_diffeomorphisms_of_the_4_sphere — discussion paragraph 2: 'For n ≥ 7 the rational homotopy groups of Diff(D^n) have been computed by Farrell and Hsiang in range 0 ≤ i < min{(n−4)/3, (n−7)/2}'; [FH] F.T. Farrell, W.C. Hsiang, On the rational homotopy groups of the diffeomorphism groups of discs, spheres and aspherical manifolds, Proc. Symp. Pure Math. 32 (1978) 403–415.

import Mathlib
import Definitions.Def_SmaleDiffS4_Basic

open SmaleDiffS4

namespace SmaleDiffS4

theorem diffDisk_rationalHomotopy_farrellHsiang (n j : ℕ)
    (h₁ : ((j + 2 : ℕ) : ℝ) < ((n : ℝ) - 4) / 3) (h₂ : ((j + 2 : ℕ) : ℝ) < ((n : ℝ) - 7) / 2) :
    Module.rank ℚ (TensorProduct ℤ ℚ (Additive (HomotopyGroup (Fin (j + 2)) (DiffDisk n) 1))) =
      if Odd n ∧ 4 ∣ (j + 2) + 1 then 1 else 0 := by sorry

end SmaleDiffS4
