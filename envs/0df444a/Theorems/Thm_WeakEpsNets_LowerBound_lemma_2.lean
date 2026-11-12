-- Prove2me | Theorems.Thm_WeakEpsNets_LowerBound_lemma_2
-- name    : WeakEpsNets.LowerBound.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:26:38.18528+00:00
-- url     : https://prove2.me/theorems/462a8593-dd01-49f9-9a74-a2d4e6e4c527
-- title:
--   Lemma 2 — Replacement Set Lemma
-- statement:
--   Fix integers $s\ge1$ and even $q\ge2$, and use the shifted grid, lift, hyperplanes, and hull families above. For every $z\in\mathbb R^{D_s}$ there is a family of finite sets $Q_{z,H}\subseteq\phi_s(B_H)$, one for each $H\in\mathcal H^{+\tau}$, such that
--   $$\forall H\ \forall C\in\mathcal C_H,\quad z\in C\ \Longrightarrow\ Q_{z,H}\cap C\ne\varnothing,\qquad \sum_{H\in\mathcal H^{+\tau}}|Q_{z,H}|\le4q^s.$$
--   Both the piercing requirement and the total replacement budget are asserted. The family is chosen after $z$, and may depend on it. This is the source's replacement result used in the counting bound.
--
--   Differences from the source:
--   - encoding: $\mathbb R^{D_s}$ with the paper's coordinates and hyperplanes indexed by positive integers → real functions on $\mathrm{Fin}(s-1)\sqcup\{(i,j)\in\mathrm{Fin}(s+1)^2:i\le j\}$ and hyperplane parameters in $(\mathrm{Fin}\,q)^s\times\mathrm{Fin}(q^2)$, interpreted as index plus one; reason: the coordinate set has exactly $D_s$ elements for $s\ge1$, and adding one bijects the parameter indices with the source's positive intervals
-- source:
--   Bhore, Browne, Zheng, Strong Lower Bounds for Weak Epsilon-Nets, STOC 2027 submission #301 (October 2026), Lemma 2 (Replacement Set Lemma), p. 10, lines 293–294; setup pp. 9–10, lines 278–290; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/301.pdf

import Mathlib
import Definitions.Def_WeakEpsNets_LowerBound_Construction

open scoped BigOperators

namespace WeakEpsNets.LowerBound

/-- Lemma 2 (Replacement Set Lemma), source p. 10, in labelled coordinates. -/
theorem lemma_2 (s q : ℕ) (hs : 1 ≤ s) (hq : 2 ≤ q) (heven : Even q)
    (z : LiftSpace s) :
    ∃ Q : HyperplaneIndex s q → Finset (LiftSpace s),
      (∀ h, Q h ⊆ liftedBlock s q h) ∧
      (∀ h, ∀ C ∈ hullFamily s q h, z ∈ C → ∃ x ∈ Q h, x ∈ C) ∧
      (∑ h : HyperplaneIndex s q, (Q h).card) ≤ 4 * q ^ s := by sorry

end WeakEpsNets.LowerBound
