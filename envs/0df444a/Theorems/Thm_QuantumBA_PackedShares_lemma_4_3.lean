-- Prove2me | Theorems.Thm_QuantumBA_PackedShares_lemma_4_3
-- name    : QuantumBA.PackedShares.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:10:54.075608+00:00
-- url     : https://prove2.me/theorems/219f2ced-df07-4fc9-9a08-d8d45c0dac58
-- title:
--   Lemma 4.3 — one election: P[Bud_v ∧ Fail_v] ≤ ξ = u2^{−τr} + b e^{−η²w/2}
-- statement:
--   Assume the sharing scheme of QBA:PackedShares (symbolic parameters, standing assumptions, $\tau,\eta\in(0,1)$) provides fresh common coins, and consider an epoch entered before the first honest decision. Let $v$ be a level-$\ell$ node with $g=g_v\ge\tau r$ counted inputs. Let $\mathrm{Fail}_v$ be the event that the members of $v$ honest at $e_v$ output different lists, or that fewer than $(g/r-\eta)w$ entries of the common output lie in $G_{\ell-1}$. Conditional on $v$'s entry history (the history at the common deadline of level $\ell-1$),
--   $$\mathbb P[\mathrm{Bud}_v\wedge\mathrm{Fail}_v]\le\xi:=u\,2^{-\tau r}+b\,e^{-\eta^2w/2}. \tag{2}$$
--
--   One election loses little of the good fraction and its honest members agree, unless the budget fails.
--
--   Differences from the source:
--   - encoding: the parameters remain symbolic until Section 6 (b, w, h, committees, forwarding graphs, capacities) → the statement holds for every parameter record X : Ctx satisfying the standing assumptions WellFormed X of §1.1, §3.1, §5.1–§5.2; reason: the standing assumptions of the sections are written as one predicate; nothing beyond them is assumed
--   - encoding: events Bud_v, Fail_v, G_ℓ, F_ℓ, 𝓔 of an execution → functions of the execution prefix up to the relevant common deadline (Bud_v at d_v, outputs at e_v, Good at the end of distribution); reason: each event is determined by that prefix
-- source:
--   Jan Olkowski, Fast Quantum Byzantine Agreement with Nearly Linear Quantum Communication, STOC 2027 submission #558 (October 2026), source.pdf SHA-256 612d0471810a0aa053891a77995d579d836cc301efd01df8e75c2bbe8ebb5383, pp. 18–19, Lemma 4.3 (PDF pp. 19–20)

import Mathlib
import Definitions.Def_QuantumBA_PackedShares_Analysis

namespace QuantumBA.PackedShares

open scoped BigOperators ENNReal Matrix

/-- Lemma 4.3 (one election). -/
theorem lemma_4_3 {n : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F] (X : Ctx n F)
    (hX : WellFormed X) (τ η : ℝ) (hτ : 0 < τ ∧ τ < 1) (hη : 0 < η ∧ η < 1)
    (hfresh : FreshCoins X) (x : Fin n → Bool) (A : Adv X) (e ℓ i : ℕ)
    (hℓ : 1 ≤ ℓ ∧ ℓ ≤ X.h) (hi : i < X.m ℓ) (hv : History F)
    (hlen : hv.length = delB X e (ℓ - 1)) (hpos : PosH X x A hv)
    (hentry : NoHonDec X x A (hv.take (epochStart X e)))
    (hg : τ * X.r ≤ gcount X x A hv e ℓ i) :
    condProb X x A hv
      {ω | Bud X x A (prefixH ω (delB X e ℓ)) e ℓ i ∧ Fail X x A η (prefixH ω (delB X e ℓ)) e ℓ i} ≤
      ENNReal.ofReal (xi X τ η) := by sorry

end QuantumBA.PackedShares
