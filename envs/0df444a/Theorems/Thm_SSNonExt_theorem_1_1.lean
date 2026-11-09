-- Prove2me | Theorems.Thm_SSNonExt_theorem_1_1
-- name    : SSNonExt.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:05:10.60249+00:00
-- url     : https://prove2.me/theorems/03840354-7637-4e2b-adfb-4bb9df168b9c
-- title:
--   Theorem 1.1 — perfect two-out-of-two sharing of $b$-bit secrets on flat $(b+2)$-bit sources with extraction error $\ge1/6$
-- statement:
--   Let $b\ge2$, $V=\mathbb F_{2^b}$, $\alpha\in V\setminus\{0,1\}$, and let $\iota:V\to\{0,1\}^b$ be any bijection. Let $\Pi_b$ be the two-out-of-two scheme of table (1), extended to keys in $\{0,1\}^{b+2}$ by the fourth branch $\bar C_i$, and let $\mathcal S_b=\{P_T:T\subseteq V\}$ be its source class on $\{0,1\}^{b+2}$. Then:
--
--   1. **Perfect correctness:** the explicit reconstruction map recovers every $b$-bit message $m$ from the two shares under every key $k\in\{0,1\}^{b+2}$, and $\Pi_b$ is perfectly correct in the sense of Definition 2.1;
--   2. **Perfect privacy:** $\Pi_b$ is perfectly private for $\mathcal S_b$ (each single share has the same law for all messages, under every $P\in\mathcal S_b$);
--   3. each share has $b+1$ bits;
--   4. every $P\in\mathcal S_b$ is uniform on a set $Z$ with $2^b\le|Z|\le2^{b+1}$, and $H_\infty(P)\ge b$;
--   5. for every $\ell\ge1$ and every function $\mathrm{Ext}:\{0,1\}^{b+2}\to\{0,1\}^\ell$,
--   $$\max_{P\in\mathcal S_b}\mathrm{TV}\big(\mathrm{Ext}(K),U_\ell\big)\ge\frac16,\qquad K\sim P.$$
--
--   Sharing and reconstruction use a constant number of operations in $\mathbb F_{2^b}$.
--
--   This answers the question of Bosley and Dodis (TCC 2007) in the negative: perfect two-out-of-two sharing of a $b$-bit secret with a $(b+2)$-bit key does not require a source class from which even one nearly uniform bit can be extracted.
--
--   **Formalization Note** The scheme and class are the paper's explicit construction, for every admissible $\alpha$ and every encoding $\iota$ (both exist for $b\ge2$). Keys, shares and messages are `Fin (b+2) → Bool`, `Fin (b+1) → Bool`, `Fin b → Bool`; item 3 holds by the share type. Privacy is total variation $0$, i.e. equality of the share laws.
--
--   Differences from the source:
--   - reading: sharing and reconstruction use a constant number of operations in 𝔽_{2^b} → the theorem is stated for the explicit scheme whose F, G and Rec are fixed constant-size formulas over 𝔽_{2^b}; reason: the clause names no computation model; it is a property of the explicit construction
--   - generalization: there are a source class 𝒮_b and a scheme → for every α ∈ 𝔽_{2^b} \ {0,1} and every bijection ι : 𝔽_{2^b} ≃ {0,1}^b, the explicit Π_b and 𝒮_b; reason: such α and ι exist for b ≥ 2, so the statement specializes to the existential
--   - encoding: each share has b + 1 bits → shares have type Fin (b+1) → Bool; reason: item 1 holds by the type
--   - encoding: keys {0,1}^{b+2}, b-bit messages, branch and tag bits → Fin (b+2) → Bool, Fin b → Bool read through ι; branch bits 00, 01, 10, 11 for L, R, C, C̄; tag bit false = untagged; reason: the paper fixes no bit assignment
--   - encoding: perfectly correct, perfectly private two-out-of-two scheme → explicit Rec correct on all keys, plus PerfectlyCorrect 2 and IsPrivate 2 0 of Definition 2.1 with one share alphabet; reason: both share alphabets are {0,1}^{b+1}
--   - encoding: max_{P∈𝒮_b} TV(Ext(K), U_ℓ) ≥ 1/6 → ∃ P ∈ 𝒮_b with TV(Ext(K), U_ℓ) ≥ 1/6; reason: 𝒮_b is finite and nonempty, so the maximum is attained
-- source:
--   Aggarwal, Secret Sharing Despite Non-Extractable Randomness, arXiv:2610.20173 (version of 2026-11-03, sha256 438a7f71…), Theorem 1.1, p.2 (PDF p.2); construction §3, pp.6–7

import Mathlib
import Definitions.Def_SSNonExt_TV
import Definitions.Def_SSNonExt_IsPrivate
import Definitions.Def_SSNonExt_bitScheme

namespace SSNonExt

/-- **Theorem 1.1 (Main result).** "For every integer b ≥ 2 there are a source class 𝒮_b on {0, 1}^{b+2}
and a perfectly correct two-out-of-two secret sharing scheme for b-bit messages that is perfectly private
for 𝒮_b, such that: 1. each share has b + 1 bits; 2. every distribution in 𝒮_b is uniform on a set of size
between 2^b and 2^{b+1}, and hence has min-entropy at least b; 3. for every ℓ ≥ 1 and every function
Ext : {0, 1}^{b+2} → {0, 1}^ℓ, max_{P∈𝒮_b} TV(Ext(K), U_ℓ) ≥ 1/6, K ∼ P. Sharing and reconstruction use a
constant number of operations in 𝔽_{2^b}."
D. Aggarwal, *Secret Sharing Despite Non-Extractable Randomness*, arXiv:2610.20173 (version of
2026-11-03, sha256 438a7f71…), Theorem 1.1, p.2 (PDF p.2); construction §3, pp.6–7.

**Formalization Note.**
* The witnesses are the paper's explicit scheme `Π_b` (table (1) plus the fourth branch of §3.2) and
  class `𝒮_b = {P_T : T ⊆ V}` (display (2)), for **every** `α ∈ 𝔽_{2^b} \ {0,1}` and **every** bit encoding
  `ι : 𝔽_{2^b} ≃ {0,1}^b`; such `α` and `ι` exist for `b ≥ 2`. The explicit formulas of `F`, `G`, `rec`
  carry "a constant number of operations in 𝔽_{2^b}".
* Keys are `Fin (b+2) → Bool`, shares `Fin (b+1) → Bool` (item 1 holds by this type), messages
  `Fin b → Bool`.
* Correctness is stated for the explicit reconstruction map on all `2^{b+2}` keys and as Definition 2.1
  with `t = 2`; perfect privacy is Definition 2.1 with `t = 2`, `δ = 0` (equal laws of each single share).
* "max over 𝒮_b ≥ 1/6" is "some `P ∈ 𝒮_b` has error ≥ 1/6" (`𝒮_b` is finite and nonempty). -/
theorem theorem_1_1 (b : ℕ) (hb : 2 ≤ b) (α : V b) (hα0 : α ≠ 0) (hα1 : α ≠ 1)
    (ι : V b ≃ (Fin b → Bool)) :
    (∀ (m : BitMsg b) (k : BitKey b), bitRec α ι (bitF ι m k) (bitG α ι m k) = m) ∧
      PerfectlyCorrect 2 (bitScheme α ι) ∧
      IsPrivate 2 0 (bitS ι) (bitScheme α ι) ∧
      (∀ P ∈ bitS ι,
        (∃ (Z : Finset (BitKey b)) (hZ : Z.Nonempty),
          P = PMF.uniformOfFinset Z hZ ∧ 2 ^ b ≤ Z.card ∧ Z.card ≤ 2 ^ (b + 1)) ∧
        (b : ℝ) ≤ minEntropy P) ∧
      (∀ ℓ : ℕ, 1 ≤ ℓ → ∀ Ext : BitKey b → (Fin ℓ → Bool),
        ∃ P ∈ bitS ι, (1 / 6 : ℝ) ≤ TV (P.map Ext) (PMF.uniformOfFintype (Fin ℓ → Bool))) := by sorry

end SSNonExt
