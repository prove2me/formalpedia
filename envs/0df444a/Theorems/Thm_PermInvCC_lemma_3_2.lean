-- Prove2me | Theorems.Thm_PermInvCC_lemma_3_2
-- name    : PermInvCC.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:23:04.507505+00:00
-- url     : https://prove2.me/theorems/78b1e2ac-0587-4dae-b467-6271a1403a02
-- title:
--   Lemma 3.2 — random linear hashing $\Pr[Hu=Hv]=2^{-m}$
-- statement:
--   Let $m\ge1$ and $n\ge2$ be integers, and let $H\in\mathbb F_2^{m\times n}$ have independent uniform binary entries. For every fixed pair of distinct vectors $u,v\in\mathbb F_2^n$,
--   $$\Pr[Hu=Hv]=2^{-m}.$$
--
--   This collision bound of Carter and Wegman drives the batch recovery of Lemma 3.4.
--
--   Differences from the source:
--   - encoding: H with independent uniform binary entries → uniform distribution on Matrix (Fin m) (Fin n) (ZMod 2), probability as a fraction of matrices; reason: the product of uniform bits is the uniform law on matrices
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Lemma 3.2, p.11

import Mathlib

namespace PermInvCC

/-- **Lemma 3.2 (Random Linear Hashing, [CW79])** (Y. Huang and Z. Ye, arXiv:2609.40116, held
version sha256 fe1797dd…, p.11). Let `m ≥ 1` be an integer, and let `H ∈ F₂^{m×n}` have
independent uniform binary entries. For every fixed pair of distinct vectors `u, v ∈ F₂ⁿ`,
`P[Hu = Hv] = 2^{−m}`.

**Formalization Note.** Independent uniform entries is the uniform distribution on the finite set
of `m × n` matrices over `ZMod 2`; the probability is the fraction of matrices with `Hu = Hv`.
`n ≥ 2` is the paper's standing assumption (p.9). -/
theorem lemma_3_2 (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n) (u v : Fin n → ZMod 2) (huv : u ≠ v) :
    ((Finset.univ.filter fun H : Matrix (Fin m) (Fin n) (ZMod 2) =>
        H.mulVec u = H.mulVec v).card : ℝ) /
      (Fintype.card (Matrix (Fin m) (Fin n) (ZMod 2)) : ℝ) = 1 / 2 ^ m := by sorry

end PermInvCC
