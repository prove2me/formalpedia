-- Prove2me | Theorems.Thm_RandLatEnum_lemma_4_1
-- name    : RandLatEnum.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:14:48.395908+00:00
-- url     : https://prove2.me/theorems/7edcef7a-d9c8-4702-94e0-ee69b7d03486
-- title:
--   Lemma 4.1 — HKZ prefix bound $P_{\lfloor td\rfloor}(B_H)/(d\ln d)\le p_H(t)+o(1)$
-- statement:
--   Let $B_H$ be an HKZ-reduced basis of a unimodular lattice of rank $d$ (size-reduced, and each Gram–Schmidt length $a_i$ equals $\lambda_1$ of the projected lattice $\pi_i(L)$). Then, uniformly for $0\le t\le1$,
--   $$
--   \frac{P_{\lfloor td\rfloor}(B_H)}{d\ln d}\le p_H(t)+o(1),\qquad p_H(t)=-\frac{1-t}{2}\ln(1-t).
--   $$
--   Precisely: for every $\varepsilon>0$ there is $D$ such that for all $d\ge D$, all such bases and all $t\in[0,1]$, $P_{\lfloor td\rfloor}(B_H)\le(p_H(t)+\varepsilon)\,d\ln d$.
--
--   This deterministic bound controls the right block (reduced by HKZ) in the block-replacement step of the proof of Theorem 1.5.
--
--   **Formalization Note** HKZ is the published Korkine–Zolotarev predicate `KannanLattice.Core.IsReduced`. The lattice is the span of linearly independent vectors in some $\mathbb R^k$ with Gram–Schmidt product $1$.
--
--   Differences from the source:
--   - generalization: a unimodular rank-d lattice (identified with ℝ^d) → the span of a linearly independent b : Fin d → ℝᵏ for any ambient k, with latticeDet b = 1; reason: the paper applies the lemma to blocks living in subspaces; k = d is the printed case
--   - encoding: o(1), uniformly for 0 ≤ t ≤ 1 → ∀ ε > 0 ∃ D, one threshold for all d ≥ D, all bases and all t ∈ [0, 1]; reason: definition of a uniform o(1)
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), Lemma 4.1, (4.3), p.19

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_KannanLattice_Core_IsReduced
import Definitions.Def_RandLatEnum_prefixLogDet
import Definitions.Def_RandLatEnum_pH

namespace RandLatEnum

open KannanLattice.Core

/-- **Lemma 4.1 (Deterministic HKZ prefix bound)** (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), Lemma 4.1, (4.3), p.19). For every HKZ
basis `B_H` of a unimodular rank-`d` lattice, uniformly for `0 ≤ t ≤ 1`,
`P_{⌊td⌋}(B_H)/(d ln d) ≤ p_H(t) + o(1)`.

**Formalization Note.** The `o(1)` is uniform in `t` and in the basis: for every `ε > 0` one
threshold `D` serves all `d ≥ D`, all bases and all `t ∈ [0, 1]`. A unimodular rank-`d` lattice is
the span of a linearly independent `b : Fin d → ℝᵏ` (any ambient `k`) with Gram–Schmidt product
`1`; HKZ is `KannanLattice.Core.IsReduced` (`a_i = λ₁(π_i(L))` and size-reduced). -/
theorem lemma_4_1 :
    ∀ ε : ℝ, 0 < ε → ∃ D : ℕ, ∀ d : ℕ, D ≤ d → ∀ (k : ℕ) (b : Fin d → EuclideanSpace ℝ (Fin k)),
      LinearIndependent ℝ b → latticeDet b = 1 → IsReduced b →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        prefixLogDet b ⌊t * d⌋₊ / (d * Real.log d) ≤ pH t + ε := by sorry

end RandLatEnum
