-- Prove2me | Theorems.Thm_SemAC02_lemma_8_7_gadget_dimension
-- name    : SemAC02.lemma_8_7_gadget_dimension
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:29:27.069279+00:00
-- url     : https://prove2.me/theorems/c2fa3a18-3ef6-475b-86e9-a04fef444159
-- title:
--   Lemma 8.7 — gadgets with a dimension bound
-- statement:
--   Fix $d\ge2$ and a sufficiently small $0<\epsilon\le1/256$. Put $L=\epsilon^{-1/(d-1)}$ and let $m$ be the smallest odd integer at least $128L^{2d-1}$. There is a gadget $g$ on $m$ variables in the sense of §8.1 — an AND-rooted AND/OR circuit of depth at most $d+1$, antitone, with $g(X)\wedge g(\overline X)=0$ for all $X$ — of size $\exp(O_d(L))$, such that the following holds. Let $U$ be the multiplier space (45) of $g$. For every $n\ge1$, with $v=nm$, and every integer $0\le k\le(1/2-\epsilon)v$,
--   $$
--   \gamma=\frac{\dim U}{H_v(k)}\ \ge\ 1-(v+1)\,n\,e^{-\epsilon^{-1/(d-1)}} .
--   $$
--
--   This is the gadget used in the proof of Theorem 8.1: with $\epsilon=(32\ln n)^{1-d}$ it has polynomial size and its multiplier space fills almost all of $\mathcal B_v^{\le k}$.
--
--   Differences from the source:
--   - encoding: O_d(L), "a sufficiently small 0 < ε ≤ 1/256" → one constant A (and ε₀ > 0) chosen before ε; ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀); reason: standard reading of O_d(·) and "for all sufficiently small ε"; the constants depend on d only
--   - encoding: m the smallest odd integer at least 128L^{2d−1} → hypotheses Odd m, 128L^{2d−1} ≤ m, and m ≤ m' for every odd m' ≥ 128L^{2d−1}; reason: these characterise the smallest such odd integer
--   - encoding: AND-rooted gadget, AND/OR circuit of depth ≤ d+1, antitone, g(X) ∧ g(X̄) = 0, size exp(O_d(L)) → IsGadget d g (also asks for the paper's normal form) and treeSize g ≤ exp(A·L); reason: the paper's circuits are in normal form by definition (p.17); the gadget is a formula, whose size is its number of nodes
--   - encoding: U as in (45), dim(U) → multiplierSpace (eval of g) n k, Module.finrank; reason: same space
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Lemma 8.7, p.66 (PDF p.68)

import Mathlib
import Definitions.Def_SemAC02_Circ
import Definitions.Def_SemAC02_IsGadget
import Definitions.Def_SemAC02_multiplierSpace
import Definitions.Def_SemAC02_Ble

namespace SemAC02

/-- **Lemma 8.7 (Gadgets with a dimension bound)** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission), Lemma 8.7, p.66): fix
`d ≥ 2` and a sufficiently small `0 < ϵ ≤ 1/256`. Put `L := ϵ^{−1/(d−1)}` and let `m` be the
smallest odd integer at least `128 L^{2d−1}`. There exists an AND-rooted gadget
`g : {0,1}^m → {0,1}` represented by an AND/OR circuit of depth at most `d + 1` and size
`exp(O_d(L))`, such that `g` is antitone and `g(X) ∧ g(X̄) = 0` for every `X`. For this gadget,
define `U` as in (45). For every `n ≥ 1`, put `v = nm`. Then, for every integer
`0 ≤ k ≤ (1/2 − ϵ)v`,
`γ = dim(U)/H_v(k) ≥ 1 − (v + 1) n e^{−ϵ^{−1/(d−1)}}` (48).

**Formalization Note** The gadget conditions are `IsGadget d g` (which also asks for the paper's
normal form). `O_d(·)` is one constant `A` before `ϵ`; size is tree size. `U` is
`multiplierSpace` of `g` (45), and `dim` is `Module.finrank`. -/
theorem lemma_8_7_gadget_dimension (d : ℕ) (hd : 2 ≤ d) :
    ∃ A ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ε ≤ 1 / 256 → ∀ m : ℕ, Odd m →
      128 * (ε ^ (-1 / ((d : ℝ) - 1))) ^ (2 * d - 1) ≤ (m : ℝ) →
      (∀ m' : ℕ, Odd m' → 128 * (ε ^ (-1 / ((d : ℝ) - 1))) ^ (2 * d - 1) ≤ (m' : ℝ) → m ≤ m') →
      ∃ g : Circ (Fin m), IsGadget d g ∧
        (g.treeSize : ℝ) ≤ Real.exp (A * ε ^ (-1 / ((d : ℝ) - 1))) ∧
        ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, (k : ℝ) ≤ (1 / 2 - ε) * ((n * m : ℕ) : ℝ) →
          1 - (((n * m : ℕ) : ℝ) + 1) * n * Real.exp (-(ε ^ (-1 / ((d : ℝ) - 1)))) ≤
            (Module.finrank (ZMod 2) (multiplierSpace (fun X => g.eval X) n k) : ℝ) /
              (Hn (n * m) k : ℝ) := by sorry

end SemAC02
