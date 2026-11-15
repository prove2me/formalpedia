-- Prove2me | Theorems.Thm_UniversalNonstochastic_Main_Supplement_lemma_20
-- name    : UniversalNonstochastic.Main.Supplement.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:28:06.126281+00:00
-- url     : https://prove2.me/theorems/b56b0955-3e63-4e45-8d81-1a9294b34e8e
-- title:
--   Lemma 20 — the first objects above $BB(s)$ and $BB_C(s)$
-- statement:
--   For $s\in\mathbb N_0$ let $\omega^*_s=\mathrm{BB}(s)+1$ and $\omega^{*C}_s=\mathrm{BB}_C(s)+1$, where $\mathrm{BB}(s)=\max\{n\in\mathbb N\mid K(n)\le s\}$ and $\mathrm{BB}_C(s)=\max\{n\in\mathbb N\mid C(n)\le s\}$ (with $\max\emptyset=0$). There is a constant $c_{27}$ such that for every $s\in\mathbb N_0$:
--
--   1. $s<K(\omega^*_s)\le s+c_{27}$, and every finite set $\Omega\subseteq\mathcal X$ with $K(\Omega)\le s-c_{27}$ satisfies $x<\omega^*_s$ for all $x\in\Omega$;
--   2. $s<C(\omega^{*C}_s)\le s+c_{27}$, and every finite set $\Omega\subseteq\mathcal X$ with $C(\Omega)\le s-c_{27}$ satisfies $x<\omega^{*C}_s$ for all $x\in\Omega$.
--
--   In particular $\omega^*_s\notin\Omega$ and $\omega^{*C}_s\notin\Omega$ for such $\Omega$. This is the paper's version of Shen's "first uncovered object"; it supplies the lower bounds of Theorems 5, 7, 8, 9, 13, 15 and 25.
--
--   Differences from the source:
--   - encoding: K(Ω) ≤ s − c27 (integer subtraction) → K(Ω) + c27 ≤ s in ℕ∞; reason: the same condition, with no truncated subtraction
--   - encoding: max Ω < ω*_s → ∀ x ∈ Ω, x < ω*_s; reason: identical for nonempty Ω; for Ω = ∅ both hold under the source's convention max ∅ := 0
--   - encoding: a constant c27 → a natural number c27; reason: complexities are integers, so a real constant can be rounded up without changing any clause
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, Lemma 20, pp.19–20 (PDF pp.19–20)

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_Complexity
import Definitions.Def_UniversalNonstochastic_Main_Supplement_Complexities

namespace UniversalNonstochastic.Main.Supplement

/-- Lemma 20, pp.19–20: with `ω*_s = BB(s) + 1` and `ω*C_s = BB_C(s) + 1`, there is a constant
`c₂₇` such that for every `s ∈ ℕ₀`:
* `s < K(ω*_s) ≤ s + c₂₇`, and every finite `Ω` with `K(Ω) ≤ s - c₂₇` has all elements
  `< ω*_s`;
* `s < C(ω*C_s) ≤ s + c₂₇`, and every finite `Ω` with `C(Ω) ≤ s - c₂₇` has all elements
  `< ω*C_s`.
`K(Ω) ≤ s - c₂₇` (integer subtraction) is written `K(Ω) + c₂₇ ≤ s`. -/
theorem lemma_20 (U : OptimalPrefixDecoder) (V : OptimalPlainDecoder) :
    ∃ c₂₇ : ℕ, ∀ s : ℕ,
      ((s : ℕ∞) < Kobj U (Nat.succPNat (busyBeaver U s)) ∧
        Kobj U (Nat.succPNat (busyBeaver U s)) ≤ (s : ℕ∞) + c₂₇ ∧
        ∀ Ω : Finset ℕ+, Kset U Ω + c₂₇ ≤ (s : ℕ∞) →
          ∀ x ∈ Ω, x < Nat.succPNat (busyBeaver U s)) ∧
      ((s : ℕ∞) < Cobj V (Nat.succPNat (busyBeaverC V s)) ∧
        Cobj V (Nat.succPNat (busyBeaverC V s)) ≤ (s : ℕ∞) + c₂₇ ∧
        ∀ Ω : Finset ℕ+, Cset V Ω + c₂₇ ≤ (s : ℕ∞) →
          ∀ x ∈ Ω, x < Nat.succPNat (busyBeaverC V s)) := by sorry

end UniversalNonstochastic.Main.Supplement
