-- Prove2me | Theorems.Thm_PPSLattice_claim_4_10
-- name    : PPSLattice.claim_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:35:40.188283+00:00
-- url     : https://prove2.me/theorems/b8aad849-7de4-4256-9e19-ea4ab275b671
-- title:
--   Claim 4.10 — $f_S$ has size $O(|S|\lceil\log N\rceil)$ and depth $O(\log N)$
-- statement:
--   There is a constant $C$ such that for every $N\ge1$ and every $S\subseteq[N]$, the set membership circuit $f_S$ of Construction 4.6, on $\lceil\log N\rceil$ input bits,
--
--   1. represents membership: $f_S(\mathrm{encvec}(i))=1$ if $i\in S$ and $0$ otherwise, for every $i\in[N]$;
--   2. has size at most $C(|S|+1)(\lceil\log N\rceil+1)$, i.e. $O(|S|\cdot\lceil\log N\rceil)$;
--   3. has depth at most $C(\lceil\log N\rceil+1)$, i.e. $O(\log N)$.
--
--   Because the noise $\|\mathbf H_{S,i}\|\le m^{O(d_f)}$ depends only on the depth, the depth bound is what makes the parameters of §4.3 polynomial in $\lambda$ and $\log N$.
--
--   Differences from the source:
--   - encoding: O(|S| · ⌈log N⌉), O(log N) → C(|S|+1)(⌈log N⌉+1), C(⌈log N⌉+1); reason: the printed products are 0 at N = 1 or S = ∅, where the constant circuits need a gate
--   - reading: the set membership circuit f_S considered in Construction 4.6 → memCircuit N S, the circuit built in the proof of Claim 4.10; reason: Construction 4.6 names f_S by its function; the proof's circuit is the one analysed
--   - encoding: a boolean circuit representation of f_S(x) = [x ∈ S] → f_S(encvec(i)) = [i ∈ S] for every i ∈ [N]; reason: indices enter the circuit through encvec (Decode Step 3)
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Claim 4.10, p.23

import Mathlib
import Definitions.Def_PPSLattice_memCircuit
import Definitions.Def_PPSLattice_circSize
import Definitions.Def_PPSLattice_circDepth
import Definitions.Def_PPSLattice_encvec
set_option autoImplicit false

namespace PPSLattice

/-- **Claim 4.10** (the set membership circuit). There is a constant `C` such that for every `N ≥ 1` and
every `S ⊆ [N]`, the circuit `f_S` of Construction 4.6 (on `⌈log N⌉` inputs)
1. represents membership: `f_S(encvec(i)) = [i ∈ S]` for every `i ∈ [N]`;
2. has size `O(|S| · ⌈log N⌉)`: at most `C(|S| + 1)(⌈log N⌉ + 1)` gates;
3. has depth `O(log N)`: at most `C(⌈log N⌉ + 1)`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Claim 4.10, p.23 ("For any S ⊆ [N], the set membership circuit f_S considered in Step 1 of KGen and
Step 3 of Decode in Construction 4.6 has a boolean circuit representation with size s_f = O(|S| · ⌈log N⌉)
and depth d_f = O(log N)").

**Formalization Note.** The `+ 1`s keep the `O(·)` bounds meaningful at `N = 1` (`⌈log N⌉ = 0`) and `S = ∅`,
where the printed products are `0` but the constant circuits need a gate or depth `1`. -/
theorem claim_4_10 : ∃ C : ℕ, ∀ N : ℕ, 1 ≤ N → ∀ S ⊆ Finset.Icc 1 N,
    (∀ i ∈ Finset.Icc 1 N, (memCircuit N S).eval (encvec N i) = [decide (i ∈ S)]) ∧
      circSize (memCircuit N S) ≤ C * (S.card + 1) * (Nat.clog 2 N + 1) ∧
      circDepth (Nat.clog 2 N) (memCircuit N S) ≤ C * (Nat.clog 2 N + 1) := by sorry

end PPSLattice
