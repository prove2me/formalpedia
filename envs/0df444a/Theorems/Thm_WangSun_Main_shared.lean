-- Prove2me | Theorems.Thm_WangSun_Main_shared
-- name    : WangSun.Main_shared
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-16T05:49:15.562032+00:00
-- url     : https://prove2.me/theorems/f0d9493a-d8dc-40b2-863b-583c5dbe4f6c
-- title:
--   Generalized hinging-hyperplane representation of CPWL functions
-- statement:
--   Let $f:\mathbb{R}^n\to\mathbb{R}$ be a continuous piecewise-linear function generated from affine functions by finitely many pointwise maxima and minima. Then $f$ is a finite sum of signed maxima of exactly $n+1$ affine functions:
--
--   $$
--   f(x)=\sum_{k=1}^{K}\sigma_k\max_{0\leq i\leq n} L_{k,i}(x),\qquad \sigma_k\in\{1,-1\}.
--   $$
--
--   This is the generalized hinging-hyperplane representation theorem. It separates the lattice-generation description of CPWL functions from a finite signed-max representation useful in approximation theory and neural-network representations.
--
--   **Formalization Note** The statement uses the shared `CPWL`, `IsHinge`, and `IsHH` definitions from `Definitions.Def_CPWL`; the dimension parameter $n$ is explicit.
-- source:
--   Koutschan, Moser, Ponomarchuk, Schicho, Generalized Hinging Hyperplanes, RICAM Report 2023-07, https://www.ricam.oeaw.ac.at/files/reports/23/rep23-07.pdf, Section 2, pp. 3–5, Lemmas 1–3 and Theorem 1; generalizing Wang and Sun (2005).

import Definitions.Def_CPWL

open Finset

namespace WangSun

theorem Main_shared {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : CPWL f) : IsHH f := by
  sorry

end WangSun
