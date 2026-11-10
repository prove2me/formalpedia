-- Prove2me | Theorems.Thm_PPSLattice_claim_4_11
-- name    : PPSLattice.claim_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:38:28.61029+00:00
-- url     : https://prove2.me/theorems/452b52d3-0ba6-48f6-b391-6958b9c5488f
-- title:
--   Claim 4.11 — the circuit of Figure 1 has size $\mathrm{poly}(\lambda,n,m,\lceil\log N\rceil,\lceil\log q\rceil)$, independent of $S,i,\mu$
-- statement:
--   There are a circuit compiler $K$ and a size function $s_C(\lambda,N,n,q)$ such that
--
--   1. $K$ maps the hardwired data of Figure 1 to a circuit in polynomial time, and $1^{s_C}$ is computable in polynomial time;
--   2. for every prime $q$, with $m=n\lceil\log q\rceil$, and all hardwired values ($\mathbf A,\mathbf s,\mathbf e,\mathbf P,\tilde{\mathbf e},tg$, $i\in[N]$, $\mu\in\{0,1\}^\lambda$, and the randomness of Remark 4.9), the circuit has at most $s_C(\lambda,N,n,q)$ gates and computes the function of Figure 1 (with the encoding of Remark 4.9) on every input $b\in\{0,1\}^{nm\lceil\log q\rceil}$;
--   3. for a constant $c$ and all $\lambda,N,n,q$,
--   $$s_C(\lambda,N,n,q)\le(\lambda+n+m+\lceil\log N\rceil+\lceil\log q\rceil+2)^c.$$
--
--   Since $s_C$ is a function of $(\lambda,N,n,q)$ only, it does not depend on $S$, $i$ or $\mu$; this is what lets MSKGen fix $\mathrm{Garb.Setup}(1^\lambda,1^{s_C},\cdot)$ before any message is encrypted.
--
--   Differences from the source:
--   - generalization: there exists a boolean circuit representation of C with size s_C → a polynomial-time compiler K producing such a circuit from the hardwired data, with 1^{s_C} polynomial-time computable; reason: implies the printed existence; skEnc and MSKGen, polynomial-time algorithms, build C and use 1^{s_C}
--   - reading: Remark 4.9: x + qr with r ← [0, ⌊2^{ℓq}/q⌋ − 1] sampled by skEnc → one independent r_j per output element of Z_q; reason: the proof of Lemma 4.22 needs independent encodings (statistical distance k·2^{−λ})
--   - encoding: s_C = poly(λ, n, m, ⌈log N⌉, ⌈log q⌉) → s_C ≤ (λ + n + m + ⌈log N⌉ + ⌈log q⌉ + 2)^c, one c for all parameters; reason: equivalent
--   - reading: hardwired values of Figure 1 → q prime, i ∈ [N], µ ∈ {0,1}^λ, encoding randomness in [0, ⌊2^{ℓq}/q⌋ − 1]; reason: Figure 1 and Remark 4.9 ('As q is prime')
--   - encoding: crs, keys, ciphertexts, messages, set descriptions; [N]; Z_q → bit strings Str (pairs via tup, numbers in binary, least significant bit first); [N] = Finset.Icc 1 N; Z_q = ZMod q; reason: Lean convention; same instances
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Claim 4.11, p.23

import Mathlib
import Definitions.Def_PPSLattice_FigCompilerValid
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- **Claim 4.11** (the circuit of Figure 1). There are a polynomial-time compiler `K` for the circuit `C` of
Figure 1 and a size function `s_C(λ, N, n, q)` with `FigCompilerValid K s_C` (so `s_C` does not depend on `S`,
`i` or `µ`), and `s_C = poly(λ, n, m, ⌈log N⌉, ⌈log q⌉)`: `s_C ≤ (λ + n + m + ⌈log N⌉ + ⌈log q⌉ + 2)^c` for one
constant `c`, with `m = n⌈log q⌉`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Claim 4.11, p.23 ("For the circuit C from Figure 1, there exists a boolean circuit representation with
size s_C = poly(λ, n, m, ⌈log N⌉, ⌈log q⌉). Moreover, s_C does not depend on S, i, or µ").

**Formalization Note.** The polynomial is the same for every parameter choice. That the circuit is
produced in polynomial time, and `1^{s_C}` computed in polynomial time, is part of `FigCompilerValid`. -/
theorem claim_4_11 : ∃ (K : Str → RestrictedDec.Circuit) (sC : ℕ → ℕ → ℕ → ℕ → ℕ) (c : ℕ),
    FigCompilerValid K sC ∧ ∀ lam N n q : ℕ,
      sC lam N n q ≤ (lam + n + n * Nat.clog 2 q + Nat.clog 2 N + Nat.clog 2 q + 2) ^ c := by sorry

end PPSLattice
