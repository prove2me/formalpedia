-- Prove2me | Theorems.Thm_RandLatEnum_block_replacement
-- name    : RandLatEnum.block_replacement
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:15:45.588448+00:00
-- url     : https://prove2.me/theorems/65261fef-4d63-48a2-be88-50f5e9589132
-- title:
--   Proof of Theorem 1.5 — block replacement: middle prefixes kept, new profile below $g_c+o(1)$
-- statement:
--   Fix $0<c<c_{\mathrm{flat}}=(2-\sqrt2)/4$. Let $L\subset\mathbb R^n$ be a unimodular lattice and $B$ a basis of $L$ with
--   $$
--   \max_{0\le k\le n}P_k(B)\le c\,n\ln n .
--   $$
--   Keep the prefix chain of $B$ between ranks $\lfloor 2cn\rfloor$ and $\lfloor(1-2c)n\rfloor$, reduce the first block by reversed dual-HKZ and the final quotient by HKZ. The resulting basis $B'$ of $L$ satisfies:
--
--   1. the middle prefix determinants are unchanged: $P_k(B')=P_k(B)$ for $\lfloor2cn\rfloor\le k\le\lfloor(1-2c)n\rfloor$;
--   2. the whole new profile lies below $g_c+o(1)$: $P_k(B')\le\bigl(g_c(k/n)+o(1)\bigr)\,n\ln n$ for $0\le k\le n$, with $g_c$ the ceiling of (7.5).
--
--   Precisely: for every $\varepsilon>0$ there is $N$ such that for every $n\ge N$, every unimodular lattice $L\subset\mathbb R^n$ and every basis $B$ as above there is a basis $B'$ of $L$ with (1) and with $P_k(B')\le(g_c(k/n)+\varepsilon)\,n\ln n$ for all $0\le k\le n$.
--
--   This deterministic step turns the area constraint of Proposition 7.1 into the lower bound $c_{\mathrm{flat}}$ on the maximal prefix.
--
--   **Formalization Note** The lattice is the lattice of a point of $X_n$; bases are ordered $\mathbb Z$-bases of it.
--
--   Differences from the source:
--   - encoding: the new profile lies below g_c + o(1) → ∀ ε > 0 ∃ N: for n ≥ N, P_k(B') ≤ (g_c(k/n) + ε) n ln n for all 0 ≤ k ≤ n, uniformly over lattices and bases; reason: the profile convention of p.18 (P_k/(n ln n) at x = k/n) and the definition of a uniform o(1)
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), proof of Theorem 1.5, p.29

import Mathlib
import Definitions.Def_RandLatEnum_X
import Definitions.Def_RandLatEnum_latticeOf
import Definitions.Def_RandLatEnum_prefixLogDet
import Definitions.Def_RandLatEnum_cFlat
import Definitions.Def_RandLatEnum_gC

namespace RandLatEnum

/-- **Block replacement** (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), proof of Theorem 1.5, p.29). Fix `0 < c < (2 − √2)/4` and suppose a
basis `B` of a unimodular lattice `L ⊂ ℝⁿ` satisfies `max_k P_k(B) ≤ c n ln n`. Keeping its prefix
chain between ranks `⌊2cn⌋` and `⌊(1 − 2c)n⌋`, reducing the first block by reversed dual-HKZ and the
final quotient by HKZ gives a basis `B'` of `L` whose middle prefix determinants are unchanged and
whose whole profile lies below `g_c + o(1)`: `P_k(B') ≤ (g_c(k/n) + o(1)) n ln n` for `0 ≤ k ≤ n`.

**Formalization Note.** Deterministic. The `o(1)` is uniform: for every `ε > 0` one `N` serves every
`n ≥ N`, every unimodular lattice and every such basis. Bases are ordered `ℤ`-bases of
`latticeOf x`; prefix determinants are those of the basis vectors in `ℝⁿ`. -/
theorem block_replacement (c : ℝ) (hc0 : 0 < c) (hc : c < cFlat) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (x : X n) (B : Module.Basis (Fin n) ℤ (latticeOf x)),
      (∀ k : ℕ, k ≤ n →
        prefixLogDet (fun i => (B i : EuclideanSpace ℝ (Fin n))) k ≤ c * n * Real.log n) →
      ∃ B' : Module.Basis (Fin n) ℤ (latticeOf x),
        (∀ k : ℕ, ⌊2 * c * n⌋₊ ≤ k → k ≤ ⌊(1 - 2 * c) * n⌋₊ →
          prefixLogDet (fun i => (B' i : EuclideanSpace ℝ (Fin n))) k =
            prefixLogDet (fun i => (B i : EuclideanSpace ℝ (Fin n))) k) ∧
        ∀ k : ℕ, k ≤ n →
          prefixLogDet (fun i => (B' i : EuclideanSpace ℝ (Fin n))) k ≤
            (gC c ((k : ℝ) / n) + ε) * n * Real.log n := by sorry

end RandLatEnum
