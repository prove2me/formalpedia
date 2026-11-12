-- Prove2me | Theorems.Thm_QuantumKtSoI_lemma_3_9
-- name    : QuantumKtSoI.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:41:20.179181+00:00
-- url     : https://prove2.me/theorems/d9813657-5335-4f24-9e84-e79f8ac3d367
-- title:
--   Lemma 3.9 — sequencing
-- statement:
--   Fix admissible glue routines with constant $c_0$. Let $e_1,e_2$ be descriptions, $g$ a glue mode, $x$ a string, and $t_1,t_2\ge1$ real deadlines; put $T=t_1+t_2+4c_0(|x|+t_1+t_2+1)$. Then for every $w$,
--   $$P_{\mathrm{SEQ}_g(e_1,e_2)}(x;T,w)\ \ge \sum_{(u,v):\ \beta_g(x,u,v)=w}P_{e_1}(x;t_1,u)\,P_{e_2}(\alpha_g(x,u);t_2,v).$$
--   If moreover $M(e_1)$ halts within $t_1$ steps on $x$ and $M(e_2)$ halts within $t_2$ steps on $\alpha_g(x,u)$ for every $u$ with $P_{e_1}(x;t_1,u)>0$, then $M(\mathrm{SEQ}_g(e_1,e_2))$ halts within $T$ steps on $x$ and equality holds for every $w$.
--
--   Sequencing is the composition interface behind every upper bound on $\mathrm{qKt}$ in the paper.
--
--   Differences from the source:
--   - generalization: the paper's glue routines, fixed once and for all and described only by their properties (p.24) → every admissible glue-routine set G (GlueRoutines.Admissible: local rules of Definition 3.1, exit within c₀(|x|+|u|+|v|+ℓ+1) steps with the glue map written and all heads on cell 0); reason: the proofs use only the p.24 properties, so the paper's routine set is one admissible instance
--   - reading: AMP loading, comparison and copy routines described only by their behaviour (pp.25–26, p.29) → routines pinned step by step in ampCore (loading sweep of 2|x|+3 steps; the two comparison heads return together; the copy routine returns copy i's output head, then copies in one sweep); reason: the paper leaves these routines unspecified beyond the stated behaviour; this is the most direct implementation of it
--   - reading: a standard injective binary encoding ⌜A⌝ of machines (p.23) → the fixed encoding CodedMachine.encode, every field written as a self-delimiting number in a fixed order; reason: the paper fixes the encoding only by its contents; by Corollary 9.5 (p.119) admissible encodings change qKt by O(log)
--   - encoding: P_M(x;t,w) = Σ ‖ψ_ρ‖² over ρ ∈ Rᵗ with ψ_ρ ≠ 0, st(ρ) final, out(ρ) = w (Definition 3.4) → Σ_{ρ ∈ recSeqs} Σ_{C final, output C = w} |ψ_ρ(C)|²; reason: equal by Lemma 3.3(iii): the support of a nonzero branch vector shares state and output; sequences outside recSeqs have ψ_ρ = 0
--   - encoding: descriptions e ∈ E charged |e| (Definition 3.6) → e : Desc charged |Desc.bits e|; reason: by Lemma 3.7 each string of E has exactly one parse, so ranging over Desc is ranging over E
--   - encoding: per-tape finite alphabets and companions of Definition 3.1 (pp.20, 23, 26) → alphabets are finite subsets of one countable symbol type Sym; the companion of a qubit tape is designated (least index for coded machines, the copy of the component's companion for constructed machines); reason: a renaming of alphabet symbols; the companion choices are the paper's own (p.23, p.26)
--   - encoding: the sum over all pairs (u, v) with β_g(x,u,v) = w → the sum over |u| ≤ ⌊t₁⌋, |v| ≤ ⌊t₂⌋; reason: a machine writes at most s output cells in s steps (p.21), so the omitted terms are 0
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Lemma 3.9, p.27

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt

open Classical

namespace QuantumKtSoI

/-- **Lemma 3.9** (Sequencing; Myrisiotis, STOC 2027 submission, held version sha256 6616571c…,
p.27). Let `e₁, e₂ ∈ E`, let `g` be a glue mode, let `x ∈ {0,1}*`, and let `t₁, t₂ ≥ 1` be real
deadlines. Put `T = t₁ + t₂ + 4c₀(|x| + t₁ + t₂ + 1)`. Then for every `w`,
`P_{SEQ_g(e₁,e₂)}(x;T,w) ≥ Σ_{(u,v): β_g(x,u,v)=w} P_{e₁}(x;t₁,u) P_{e₂}(α_g(x,u);t₂,v)`.
If moreover `M(e₁)` halts within `t₁` steps on `x`, and `M(e₂)` halts within `t₂` steps on
`α_g(x,u)` for every `u` with `P_{e₁}(x;t₁,u) > 0`, then `M(SEQ_g(e₁,e₂))` halts within `T` steps
on `x` and equality holds for every `w`.

**Formalization Note** `c₀` is the constant `G.c0` of the admissible glue routines `G`. The sum
over all pairs `(u, v)` is taken over `|u| ≤ ⌊t₁⌋`, `|v| ≤ ⌊t₂⌋`: the other terms vanish, since
a machine writes at most `s` output cells in `s` steps (p.21). -/
theorem lemma_3_9 (G : GlueRoutines) (hG : G.Admissible) (e₁ e₂ : Desc) (g : Glue)
    (x : List Bool) (t₁ t₂ : ℝ) (ht₁ : 1 ≤ t₁) (ht₂ : 1 ≤ t₂) :
    let T : ℝ := t₁ + t₂ + 4 * G.c0 * (x.length + t₁ + t₂ + 1)
    (∀ w : List Bool,
        ∑ u ∈ stringsUpTo ⌊t₁⌋₊, ∑ v ∈ stringsUpTo ⌊t₂⌋₊ with g.beta x u v = w,
            e₁.probR G x t₁ u * e₂.probR G (g.alpha x u) t₂ v ≤
          (Desc.seq g e₁ e₂).probR G x T w) ∧
      ((e₁.machine G).HaltsWithin x ⌊t₁⌋₊ →
        (∀ u, 0 < e₁.probR G x t₁ u → (e₂.machine G).HaltsWithin (g.alpha x u) ⌊t₂⌋₊) →
        ((Desc.seq g e₁ e₂).machine G).HaltsWithin x ⌊T⌋₊ ∧
          ∀ w : List Bool, (Desc.seq g e₁ e₂).probR G x T w =
            ∑ u ∈ stringsUpTo ⌊t₁⌋₊, ∑ v ∈ stringsUpTo ⌊t₂⌋₊ with g.beta x u v = w,
              e₁.probR G x t₁ u * e₂.probR G (g.alpha x u) t₂ v) := by sorry

end QuantumKtSoI
