-- Prove2me | Theorems.Thm_Schnir_schnirelmann_ineq
-- name    : Schnir.schnirelmann_ineq
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T22:48:05.414989+00:00
-- url     : https://prove2.me/theorems/f6a4e284-bb0f-4c78-9437-6f4bbd2f9bd6
-- title:
--   Schnirelmann's inequality $\sigma(D+E)\ge\sigma(D)+\sigma(E)-\sigma(D)\sigma(E)$
-- statement:
--   Let $D,E\subseteq\mathbb{Z}_{\ge 0}$ with $0\in D$ and $0\in E$, and let $\sigma$ be the Schnirelmann density. Then
--
--   $$
--   \sigma(D+E) \;\ge\; \sigma(D)+\sigma(E)-\sigma(D)\,\sigma(E),
--   $$
--
--   where $D+E=\{d+e: d\in D,\ e\in E\}$.
--
--   This is Schnirelmann's classical additive inequality, equivalently $1-\sigma(D+E)\le(1-\sigma(D))(1-\sigma(E))$. It applies to any sets containing $0$ and is not specific to primes.
--
--   **Formalization Note** $\sigma$ is Mathlib's `schnirelmannDensity`, with classical decidability. $D+E$ is the pointwise sumset.
-- source:
--   An explicit elementary constant for sums of primes (unpublished note, September 2026), eq. (17), §6

import Mathlib
import Definitions.Def_Schnir_defs

namespace Schnir

open Pointwise Classical in
theorem schnirelmann_ineq (D E : Set ℕ) (hD : 0 ∈ D) (hE : 0 ∈ E) :
    schnirelmannDensity D + schnirelmannDensity E
      - schnirelmannDensity D * schnirelmannDensity E ≤ schnirelmannDensity (D + E) := by sorry

end Schnir
