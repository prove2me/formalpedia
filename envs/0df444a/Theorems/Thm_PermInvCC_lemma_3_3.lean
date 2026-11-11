-- Prove2me | Theorems.Thm_PermInvCC_lemma_3_3
-- name    : PermInvCC.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:26:02.593297+00:00
-- url     : https://prove2.me/theorems/42be183e-b272-497c-b3a2-ff4730853c10
-- title:
--   Lemma 3.3 — estimating the disagreement count within a factor $\kappa$ with $O_\delta(\log n)$ bits
-- statement:
--   For each fixed $\delta\in(0,1)$ there are a constant $\kappa\ge1$ and a constant $C$ such that for every $n\ge2$ there is a public-coin protocol, on binary strings $\xi,\eta\in\mathbb F_2^n$, using at most $C\log n$ bits, with the following properties. Let $k=|\{i:\xi_i\ne\eta_i\}|$ be the number of disagreements; the protocol outputs the same value $\tilde k$ to both parties, and
--
--   1. if $k=0$, the output is always $0$;
--   2. if $k>0$, then $\Pr[k/\kappa\le\tilde k\le\kappa k]\ge1-\delta$;
--   3. each nonzero output is an integer power of two at most $n$.
--
--   The estimate sets the sampling rate in the protocol of Theorem 3.1.
--
--   Differences from the source:
--   - encoding: O_δ(log n) bits → cost ≤ C · log₂ n with C chosen after δ and before n; reason: the O-constant depends only on δ; n ≥ 2 makes log₂ n ≥ 1
--   - encoding: outputs the same value to both parties → the output is the leaf label of the protocol tree; reason: the transcript and public coins determine it, so both parties know it
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Lemma 3.3, p.11 (restated p.46)

import Mathlib
import Definitions.Def_PermInvCC_PubProtocol

namespace PermInvCC

/-- **Lemma 3.3 (Estimating the Disagreement Count)** (Y. Huang and Z. Ye, arXiv:2609.40116, held
version sha256 fe1797dd…, p.11). For each fixed `δ ∈ (0, 1)`, there is a constant `κ ≥ 1` and a
public-coin protocol using `O_δ(log n)` bits with the following property. On binary strings with
`k` disagreements it outputs the same value `k̃` to both parties. If `k = 0`, the output is always
zero. If `k > 0`, then `P[k/κ ≤ k̃ ≤ κk] ≥ 1 − δ`. Each nonzero output is an integer power of two
at most `n`.

**Formalization Note.** `O_δ(log n)` is an explicit constant `C` chosen after `δ` and before `n`
(with `n ≥ 2`, the standing assumption). The protocol's output is transcript-determined, hence
the same for both parties. "Always" means for every value of the public coins. -/
theorem lemma_3_3 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ κ : ℝ, 1 ≤ κ ∧ ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      ∃ P : PubProtocol (Fin n → ZMod 2) (Fin n → ZMod 2) ℕ,
        (P.cost : ℝ) ≤ C * Real.logb 2 n ∧
        (∀ ω ξ η, P.run ω ξ η ≠ 0 → ∃ j : ℕ, P.run ω ξ η = 2 ^ j ∧ 2 ^ j ≤ n) ∧
        ∀ ξ η : Fin n → ZMod 2,
          let k := (Finset.univ.filter fun i => ξ i ≠ η i).card
          (k = 0 → ∀ ω, P.run ω ξ η = 0) ∧
          (0 < k → 1 - δ ≤
            P.prob ξ η (fun k' => (k : ℝ) / κ ≤ (k' : ℝ) ∧ (k' : ℝ) ≤ κ * k)) := by sorry

end PermInvCC
