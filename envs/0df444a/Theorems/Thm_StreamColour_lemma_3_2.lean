-- Prove2me | Theorems.Thm_StreamColour_lemma_3_2
-- name    : StreamColour.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:53:54.717173+00:00
-- url     : https://prove2.me/theorems/bd689a5d-011f-4aeb-bf79-bd39c0f2d31d
-- title:
--   Lemma 3.2 — the capacity-$b$ sketch: $O(b\log n)$ bits, exact sparse recovery, rejection except with probability $n/p$
-- statement:
--   Let $p$ be a prime with $n^{50}<p<2n^{50}$, and $1\le b\le n$.
--
--   1. A capacity-$b$ sketch and its seed occupy at most $c\,b\,\ell(n)$ bits, for an absolute constant $c$.
--   2. Some program computes the decoder's answer from $n,b,p,\xi$ and the measurements, writes at most $Ab$ memory cells of $c_w\ell(n)$ bits on every run, and halts.
--   3. At most one signed vector of support at most $b$ agrees with any given moments.
--   4. For fixed $x\in\{-1,0,1\}^n$ with at most $b$ nonzero coordinates, the decoder returns $x$ for every seed.
--   5. For fixed $x\in\{-1,0,1\}^n$ with more than $b$ nonzero coordinates, under a uniform seed, the decoder accepts with probability at most $n/p$.
--   6. For a 0–1 vector with at most $b$ nonzero coordinates, the moments alone determine it, with no seed.
--
--   This is the recovery primitive of both algorithms: subtracting a sketch from the sketch of a known reference set yields a sparse signed difference from which a whole neighbourhood is recovered.
--
--   Differences from the source:
--   - encoding: $O(b\log n)$ bits and workspace → $c\,b\,\ell(n)$ bits, and at most $Ab$ cells of word size $c_w\ell(n)$, with $c,A,c_w$ absolute; reason: $\ell(n)$ is $\log n$ written with $n+1$; for $n=1$ no prime lies in the range, so the case is vacuous
--   - reading: "a decoder", with no machine named → a single `DynBrooks.Program` with input $n,b,p,\xi$, the moments and the fingerprint, and output $0$ for a rejection, or $1$ and then $y_u+1$ for each coordinate; reason: the workspace claim needs a machine, as for the goal; the sketch is held in memory by the program, which is within $O(b)$ cells
--   - generalization: for a 0–1 vector whose exact support size is known, the moments alone suffice → no knowledge of the exact size is used, and uniqueness of a moment-consistent candidate is stated for all moments; reason: the proof shows both, and the printed claim is a special case
-- source:
--   Chakraborty, Chatterjee, Kundu, Mishra, Streaming Graph Colouring Meets Molloy–Reed via Kernelization (STOC 2027 submission, preprint, sha256 31a813b319e4af3fd96deb52ecd284fc2c478368ab1d9064bb951dcc884cc105), Lemma 3.2, p.22 (PDF 24)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_StreamColour_Params
import Definitions.Def_StreamColour_StreamModel
import Definitions.Def_StreamColour_Sketch

namespace StreamColour

/-- Chakraborty, Chatterjee, Kundu, Mishra, *Streaming Graph Colouring Meets Molloy–Reed via Kernelization* (STOC 2027 submission, sha256 31a813b3…), Lemma 3.2, p.22 (PDF 24).

A capacity-`b` sketch and its seed occupy `O(b log n)` bits. For a fixed signed `x` independent of the seed the
decoder recovers `x` if its support has size at most `b`; otherwise it rejects except with probability at most
`n/p`. The decoder uses `O(b log n)` additional workspace and unrestricted time. For a 0–1 vector of support at
most `b`, the moments alone suffice.

**Formalization Note.** The clauses, in order: the bit count, with `c` absolute; a single program, of word size
`cw · ℓ(n)`, that computes `decode` from `n, b, p, ξ` and the measurements, writing at most `A * b` cells on every
run (so `O(b log n)` bits) and halting on every coin tape; at most one candidate for any moments; exact recovery
for every seed when the support has size at most `b`; the rejection bound under a uniform seed (`∀ x` before the
seed is "independent of the seed"); and, for 0–1 vectors, recovery by the seedless `candidate`. The range of `p` is
the page's, so `n = 1` has no such prime and is vacuous. The bound is in `ℓ(n)`, i.e. `log n` written with `n + 1`. -/
theorem lemma_3_2 :
    (∃ c : ℕ, ∀ n b p : ℕ, p.Prime → n ^ 50 < p → p < 2 * n ^ 50 → 1 ≤ b → b ≤ n →
      sketchBits b p ≤ c * b * ell n) ∧
    (∃ (P : DynBrooks.Program) (cw A : ℕ), ∀ (n b p : ℕ) [Fact p.Prime] (ξ : ZMod p)
        (meas : Measurements p b),
      n ^ 50 < p → p < 2 * n ^ 50 → 1 ≤ b → b ≤ n →
      let w := cw * ell n
      let c₀ := initConfig w (decoderInput n b p ξ meas)
      (∀ (ω : ℕ → BitVec w) (t : ℕ), (DynBrooks.run P ω c₀ t).written.card ≤ A * b) ∧
      ∀ ω : ℕ → BitVec w, ∃ t,
        P[(DynBrooks.run P ω c₀ t).pc]? = some DynBrooks.Instr.halt ∧
        (DynBrooks.run P ω c₀ t).output = decodeOutput n (decode n p b ξ meas)) ∧
    ∀ (n b p : ℕ) [Fact p.Prime], n ^ 50 < p → p < 2 * n ^ 50 → 1 ≤ b → b ≤ n →
      (∀ (m : Fin (2 * b) → ZMod p) (y₁ y₂ : Fin n → ℤ),
        IsCandidate p b m y₁ → IsCandidate p b m y₂ → y₁ = y₂) ∧
      ∀ x : Fin n → ℤ, IsSigned x →
        ((supp x).card ≤ b → ∀ ξ : ZMod p, decode n p b ξ (sk p b ξ x) = some x) ∧
        (b < (supp x).card →
          unifProb (ZMod p) (fun ξ => (decode n p b ξ (sk p b ξ x)).isSome = true) ≤
            (n : ℝ) / (p : ℝ)) ∧
        ((∀ u, x u = 0 ∨ x u = 1) → (supp x).card ≤ b →
          candidate n p b (moments p b x) = some x) := by sorry

end StreamColour
