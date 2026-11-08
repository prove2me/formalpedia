-- Prove2me | Theorems.Thm_ValiantModel_lemma_4_8
-- name    : ValiantModel.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:37:13.19148+00:00
-- url     : https://prove2.me/theorems/ecd013d4-160b-4494-a1f4-69d211d4c36f
-- title:
--   Lemma 4.8, p.26 — $|\mathrm{Cl}_k(H_d)|\le 2^{(d+1)(k+1)}$ and $\mathrm{VC}(\mathrm{Cl}_k(H_d))\le(d+1)(k+1)$
-- statement:
--   For all $d,k\in\mathbb N$ and every class $H_d$ of Boolean functions on $\{0,1\}^d$,
--
--   $$
--   |\mathrm{Cl}_k(H_d)|\le 2^{(d+1)(k+1)},
--   $$
--
--   and consequently
--
--   $$
--   \mathrm{VC}(\mathrm{Cl}_k(H_d))\le(d+1)(k+1).
--   $$
--
--   Although a closure intersects an unbounded number of hypotheses, the closure class is indexed by transcripts, which keeps it small. This is the counting input to Theorem 4.9.
--
--   **Formalization Note** The VC bound is stated in `ℕ∞`, which is where `vcDim` takes its values.
--
--   Differences from the source:
--   - generalization: d ∈ N, with the sequence starting at H₁ → `d = 0` is allowed as well; reason: the bound holds there by the same count; the printed range is the case d ≥ 1
--   - encoding: a closure, a subset of the cube → its indicator function; reason: a subset and its indicator determine each other
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), p.26 (PDF p.28), Lemma 4.8

import Mathlib
import Definitions.Def_HighDimProb_Chaining_VcDim
import Definitions.Def_ValiantModel_ClosureClass

open HighDimProb.Chaining

namespace ValiantModel

/-- **Lemma 4.8**, arXiv:2605.13840 (version held), p.26 (PDF p.28). For every `d, k ∈ ℕ`,
`|Cl_k(Hd)| ≤ 2^((d+1)(k+1))`, and consequently `VC(Cl_k(Hd)) ≤ (d+1)(k+1)`.

**Formalization Note.** `Hd` is any set of Boolean functions on `{0,1}^d`, and `d = 0`, `k = 0` are
allowed. `Set.ncard` is the true cardinality on the finite type. The VC bound is in `ℕ∞`. -/
theorem lemma_4_8 (d k : ℕ) (Hd : Set (Hypothesis d)) :
    (ClosureClass Hd k).ncard ≤ 2 ^ ((d + 1) * (k + 1)) ∧
      vcDim (ClosureClass Hd k) ≤ (((d + 1) * (k + 1) : ℕ) : ℕ∞) := by sorry

end ValiantModel
