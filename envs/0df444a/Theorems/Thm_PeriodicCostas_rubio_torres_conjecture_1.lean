-- Prove2me | Theorems.Thm_PeriodicCostas_rubio_torres_conjecture_1
-- name    : PeriodicCostas.rubio_torres_conjecture_1
-- status  : Disproved
-- author  : @shivm
-- created : 2026-10-04T14:25:37.855143+00:00
-- url     : https://prove2.me/theorems/f2732909-8aec-45d0-afe0-8943f5d2c80e
-- title:
--   Rubio–Torres Conjecture 1: periodic Costas arrays have order $2^k$
-- statement:
--   **Conjecture 1 (Rubio–Torres).** Let $k\ge l\ge1$ and let $\varphi:[a_1]\times\cdots\times[a_k]\to[b_1]\times\cdots\times[b_l]$ define a periodic Costas array. Then $\prod_{i=1}^k a_i=2^k$ (equivalently every $a_i=2$, since sides are $\ge2$).
--
--   $k\ge l$ is the source's normalization; $l\ge1$ excludes the degenerate case.
-- source:
--   I. Rubio and J. Torres, Multidimensional Costas Arrays and Their Periodicity, IEEE Trans. Inf. Theory 69(8) (2023) 5032-5040, https://arxiv.org/abs/2208.02378, doi:10.1109/TIT.2023.3264951; Rubio-Torres 2023 (arXiv:2208.02378v1), Section 4, Conjecture 1 (p. 16); Definitions 2-4 (pp. 6, 8)

import Definitions.Def_PeriodicCostasArray

namespace PeriodicCostas

theorem rubio_torres_conjecture_1 {k l : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k)
    (a : Fin k → ℕ) (b : Fin l → ℕ) (φ : (Fin k → ℤ) → (Fin l → ℤ))
    (hA : IsPeriodicCostas a b φ) :
    ∏ i, a i = 2 ^ k := by sorry

end PeriodicCostas
