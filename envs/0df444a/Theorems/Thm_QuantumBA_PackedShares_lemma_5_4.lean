-- Prove2me | Theorems.Thm_QuantumBA_PackedShares_lemma_5_4
-- name    : QuantumBA.PackedShares.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:10:53.445928+00:00
-- url     : https://prove2.me/theorems/fd57932b-4291-46d1-af63-4f5777748809
-- title:
--   Lemma 5.4 — protection along a path
-- statement:
--   Consider QBA:PackedShares with symbolic parameters, a good array $y$ (its dealer is not corrupted by the end of distribution) whose registers have moved along the committees $C_1,\dots,C_\ell$ of its path, with forwarding graphs satisfying (10) for sampler error $\rho$, $\gamma+2\rho+D_j^{-1}<\theta$ for all $j$ and $(\gamma+\rho)|C_1|\le\sigma(|C_1|)$, where $\gamma=1/3-\varepsilon/2$ and $\theta=1/3-\varepsilon/4$. Let $s$ be a boundary no earlier than the end of the round in which the array was transferred out of $C_{\ell-1}$ (the distribution round if $\ell=1$). Assume
--
--   1. for each $j<\ell$, at most $\gamma|C_j|$ members of $C_j$ were corrupted by the end of the transfer round out of $C_j$, and all members of $C_j$ honest at the end of that round transferred the array;
--   2. at most $\gamma|C_\ell|$ members of $C_\ell$ are corrupted by $s$.
--
--   The epoch is entered before the first honest decision (the scope of the survival analysis, §3.3, in which $\mathrm{Good}$ is defined). Then every word of the array that reached $C_\ell$ and whose transfer out of $C_\ell$ has not begun by $s$ is protected at $s$, whether or not it has been opened.
--
--   Only faults present at a completed transfer enter its fault set; this is why protection survives adaptive corruption.
--
--   Differences from the source:
--   - encoding: the parameters remain symbolic until Section 6 (b, w, h, committees, forwarding graphs, capacities) → the statement holds for every parameter record X : Ctx satisfying the standing assumptions WellFormed X of §1.1, §3.1, §5.1–§5.2; reason: the standing assumptions of the sections are written as one predicate; nothing beyond them is assumed
--   - reading: blocks are those whose round has begun by s; a register not consumed by such a block counts as stored, also before delivery → a block of holder u belongs to the circuit at s if its round has begun by s and u, active at the start of that round, transfers the word; its outputs are inputs of the receiver’s block (if the receiver’s block exists and takes that in-edge) or stored at the receiver; reason: the circuit of §5.3 for QBA:PackedShares; a holder corrupted before its round has no block and its stored registers are exposed, which gives the same marks as an exposed block
-- source:
--   Jan Olkowski, Fast Quantum Byzantine Agreement with Nearly Linear Quantum Communication, STOC 2027 submission #558 (October 2026), source.pdf SHA-256 612d0471810a0aa053891a77995d579d836cc301efd01df8e75c2bbe8ebb5383, p. 30, Lemma 5.4 (PDF p. 31)

import Mathlib
import Definitions.Def_QuantumBA_PackedShares_Analysis

namespace QuantumBA.PackedShares

open scoped BigOperators ENNReal Matrix

/-- Lemma 5.4 (protection along a path). -/
theorem lemma_5_4 {n : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F] (X : Ctx n F)
    (hX : WellFormed X) (ρ : ℝ) (y ℓ : ℕ) (hy : 1 ≤ y ∧ y ≤ X.N) (hℓ : 1 ≤ ℓ ∧ ℓ ≤ X.h)
    (hpath : ∀ j, 1 ≤ j → j < ℓ → hasTransfer X j)
    (hsamp : ∀ j, 1 ≤ j → j < ℓ → SamplerProp X ρ j (anc X j y))
    (hslack : ∀ j, 1 ≤ j → j < ℓ → gam X + 2 * ρ + 1 / (X.D j : ℝ) < 1 / 3 - X.ε / 4)
    (hC1 : (gam X + ρ) * (X.comm 1 (anc X 1 y)).card ≤ X.sigma (X.comm 1 (anc X 1 y)).card)
    (x : Fin n → Bool) (A : Adv X) (e : ℕ) (h : History F) (hpos : PosH X x A h)
    (hentry : NoHonDec X x A (h.take (epochStart X e)))
    (hgood : y ∈ Good X x A h e)
    (hs : bnd n (blockRound X e (ℓ - 1)) ≤ h.length)
    (hpast : ∀ j, 1 ≤ j → j < ℓ →
      (((X.comm j (anc X j y)) ∩ badAt X x A h (bnd n (blockRound X e j))).card : ℝ) ≤
          gam X * (X.comm j (anc X j y)).card ∧
      ∀ u ∈ X.comm j (anc X j y), u ∉ badAt X x A h (bnd n (blockRound X e j)) →
        y ∈ outsE X (viewAt X x A h (startB n (blockRound X e j)) u) e j (anc X j y))
    (hcur : (((X.comm ℓ (anc X ℓ y)) ∩ badAt X x A h h.length).card : ℝ) ≤
      gam X * (X.comm ℓ (anc X ℓ y)).card) :
    ∀ lb ∈ arrayLabels X, ℓ ≤ lb.lev X.h →
      (lb.lev X.h = ℓ ∨ ¬ hasTransfer X ℓ ∨ h.length ≤ startB n (blockRound X e ℓ)) →
      Protected X x A h h.length e y lb := by sorry

end QuantumBA.PackedShares
