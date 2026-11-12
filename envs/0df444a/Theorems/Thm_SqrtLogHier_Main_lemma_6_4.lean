-- Prove2me | Theorems.Thm_SqrtLogHier_Main_lemma_6_4
-- name    : SqrtLogHier.Main.lemma_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:57:35.633717+00:00
-- url     : https://prove2.me/theorems/a91af1af-f016-4185-a08f-4205f580db64
-- title:
--   Lemma 6.4 — LF and ILF of a binary text through rank and select on the BWT without its r*-th symbol
-- statement:
--   Let $T\in\{0,1\}^n$ with $n\ge2$, $a=T[n]$, $r^*=\mathrm{ISA}_T[1]$, $C_0=0$, $C_1=|\{j:T[j]=0\}|$, $\delta_c=[c=a]$, let $D$ be $\mathrm{BWT}_T$ with position $r^*$ deleted and $f_c$ the number of occurrences of $c$ in $D$. Then $z=C_a+1$ satisfies $z=\mathrm{ISA}_T[n]=\mathrm{LF}_T[r^*]$, and
--
--   $$\mathrm{LF}_T[s+[s\ge r^*]]=C_{D[s]}+\delta_{D[s]}+\mathrm{rank}_D(s,D[s])\ \ (s\in[1..n)),\qquad \mathrm{select}_D(h,c)=p-[p>r^*]\ \text{ for }p=\mathrm{ILF}_T[C_c+\delta_c+h],\ h\in[1..f_c].$$
--
--   This is Lemma 6.4 of the paper (p. 38), a combinatorial identity used in the reductions between batched LF and ILF queries (Theorems 6.5, 6.6). It needs no machine model.
--
--   Differences from the source:
--   - encoding: T ∈ {0,1}^n, BWT_T, LF_T, ILF_T, select_D(h, c) = ∞ when fewer than h occurrences → T a list of naturals with symbols < 2; the 1-based arrays of this mission; select as the published CentralStrQ.select with values in ℕ∞; D = BWT_T with entry r* removed (List.eraseIdx); reason: Lean conventions; same instances
--   - encoding: [s ≥ r*], [p > r*], δ_c = [c = a] (Iverson brackets) → if … then 1 else 0; p − [p > r*] in ℕ; reason: p > r* ≥ 1 when the bracket is 1, so no truncation occurs
-- source:
--   Kempa, Kociumaka, A Unified and Robust Theory of Lower and Upper Bounds for the √log n Barrier, STOC 2027 submission (manuscript sha256 7a17340d…), p. 38, Lemma 6.4

import Mathlib
import Definitions.Def_CentralStrQ_Strings
import Definitions.Def_CentralStrQ_PLCPBitvector
import Definitions.Def_SqrtLogHier_Main_StringArrays

set_option autoImplicit false

namespace SqrtLogHier.Main

/-- Lemma 6.4 (p. 38): for binary `T` with `n ≥ 2`, `a = T[n]`, `r* = ISA_T[1]`, `C_0 = 0`,
`C_1 = |{j : T[j] = 0}|`, `δ_c = [c = a]`, and `D` the string `BWT_T` with position `r*` deleted,
`z = C_a + 1` satisfies `z = ISA_T[n] = LF_T[r*]`, and LF and ILF are given by rank and select
on `D`. -/
theorem lemma_6_4 (T : List ℕ) (hT : ∀ a ∈ T, a < 2) (hn : 2 ≤ T.length) :
    let n := T.length
    let a := T.getD (n - 1) 0
    let rs := CentralStrQ.ISA T 1
    let C : ℕ → ℕ := fun c => if c = 0 then 0 else T.count 0
    let δ : ℕ → ℕ := fun c => if c = a then 1 else 0
    let D := (bwt T).eraseIdx (rs - 1)
    let z := C a + 1
    (z = CentralStrQ.ISA T n ∧ z = LF T rs) ∧
    (∀ s : ℕ, 1 ≤ s → s < n →
      let p := s + (if rs ≤ s then 1 else 0)
      let c := D.getD (s - 1) 0
      LF T p = C c + δ c + rank D s c) ∧
    (∀ c : ℕ, c < 2 → ∀ h : ℕ, 1 ≤ h → h ≤ D.count c →
      let p := ILF T (C c + δ c + h)
      CentralStrQ.select D h c = ((p - (if rs < p then 1 else 0) : ℕ) : ℕ∞)) := by sorry

end SqrtLogHier.Main
