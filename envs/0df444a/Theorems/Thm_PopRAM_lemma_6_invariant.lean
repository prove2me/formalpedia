-- Prove2me | Theorems.Thm_PopRAM_lemma_6_invariant
-- name    : PopRAM.lemma_6_invariant
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:23:41.851201+00:00
-- url     : https://prove2.me/theorems/7f454b9e-3509-4f0e-a522-aa15666e6569
-- title:
--   §3 (4) / proof of Lemma 6 — the binary-search invariant $0\le A-|Z|<2^{\ell+1}$, and the stored word equals $A$
-- statement:
--   Let $w\ge2$ and $0\le A<2^{w-1}$. Run the loop $\ell=w-2,\dots,0$ from $Z=0$, setting $b_\ell=1$ and $Z\leftarrow Z+2^\ell$ if $Z+2^\ell\le A$, and $b_\ell=0$ otherwise. Then
--
--   1. before bit $\ell$: $\;0\le A-Z<2^{\ell+1}$;
--   2. after bit $0$: $Z=A$;
--   3. bit $\ell$ of the $w$-bit word of $A$ is $b_\ell$ for $\ell\le w-2$, its sign bit $w-1$ is $0$, and its two's-complement value is $A$.
--
--   This is the correctness of the unary-to-binary conversion of the MC+ simulation (Protocol 13, Lemma 6), given correct majority comparisons.
--
--   Differences from the source:
--   - encoding: majority comparison of |Z| and |X_i| by the MC+ majority protocol → exact comparison Z + 2^ℓ ≤ A; reason: the invariant concerns the deterministic loop; the comparison is correct whp by Theorem 8
--   - encoding: the loop ℓ = w − 2, …, 0 'initially ℓ = w − 2' → w ≥ 2; reason: at w = 1 there is no value bit and the initial ℓ is undefined
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), §3 technique (4), p.11 (PDF p.12), ll.444–447; proof of Lemma 6, p.25 (PDF p.26)

import Mathlib
import Definitions.Def_PopRAM_Greedy

set_option autoImplicit false

namespace PopRAM

/-- **The binary-search invariant of U2Bconversion** (Gąsieniec, Grodzicki, Stachowiak,
arXiv:2611.06178, held version sha256 f13223b3…, §3 technique (4), p.11, PDF p.12, ll.444–447,
used in the proof of Lemma 6, p.25, PDF p.26). "The invariant is 0 ≤ |X_i| − |Z| < 2^{ℓ+1} before
bit ℓ, initially ℓ = w − 2 and Z = ∅. The comparison and choice reduce the residual to [0, 2^ℓ);
after bit 0 it is zero. The untouched sign bit remains 0 from register initialisation, so the stored
word equals |X_i|."

For `w ≥ 2` and `0 ≤ A < 2^{w−1}` (`A = |X_i|`), running the loop `ℓ = w − 2, …, 0` from `Z = 0`:
1. before bit `ℓ`, `Z ≤ A < Z + 2^{ℓ+1}`;
2. after bit `0`, `Z = A`;
3. the word whose bit `ℓ` is the bit written at `ℓ` (for `ℓ ≤ w − 2`) and whose sign bit `w − 1`
   is `0` is the `w`-bit word of `A`, and its signed (U2) value is `A`. -/
theorem lemma_6_invariant (w A : ℕ) (hw : 2 ≤ w) (hA : A < 2 ^ (w - 1)) :
    (∀ ℓ ≤ w - 2, greedyZ A w (w - 2 - ℓ) ≤ A ∧ A < greedyZ A w (w - 2 - ℓ) + 2 ^ (ℓ + 1)) ∧
    greedyZ A w (w - 1) = A ∧
    (∀ ℓ < w, (BitVec.ofNat w A).getLsbD ℓ = (if ℓ ≤ w - 2 then greedyBit A w ℓ else false)) ∧
    (BitVec.ofNat w A).toInt = A := by sorry

end PopRAM
