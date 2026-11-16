-- Prove2me | Theorems.Thm_PHIP1887_central_jet_identity
-- name    : PHIP1887.central_jet_identity
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:21:30.174793+00:00
-- url     : https://prove2.me/theorems/852a452e-d308-4262-870e-c4eaaa0f84de
-- title:
--   Polynomial identity for a central Euler jet
-- statement:
--   Let $y\in\mathbb C$ and $k\in\mathbb N$, with $0\in\mathbb N$. Write $z=y(1-y)$. Then
--
--   $$k^2z^k(1-2y)^2-2kz^{k+1}=k^2z^k-2k(2k+1)z^{k+1}.$$
--
--   This polynomial identity simplifies the second Euler jet of a central atom. The statement is algebraic: it does not assert differentiation under an infinite sum or a sign for a spectral tower.
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandao Bueno. PHIP-1887, declaration central_jet_identity in PHIP-1887_AXLE.lean; PF28 FINAL 15 November 2026, section 166.1. https://app.notion.com/p/41898395ac6e815bba24d5e67b9ec0f9 . Elementary algebraic lemma; no novelty claim.

import Mathlib

theorem PHIP1887.central_jet_identity (y : ℂ) (k : ℕ) :
    (k : ℂ)^2 * (y*(1-y))^k * (1-2*y)^2
      - 2*(k : ℂ)*(y*(1-y))^(k+1)
    = (k : ℂ)^2 * (y*(1-y))^k
      - 2*(k : ℂ)*(2*(k : ℂ)+1)*(y*(1-y))^(k+1) := by sorry
