-- Prove2me | Theorems.Thm_TargetedSamplers_Supplement_theorem_8_3
-- name    : TargetedSamplers.Supplement.theorem_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:17:02.407205+00:00
-- url     : https://prove2.me/theorems/b3e5d43f-500e-48a9-8f55-6309f6d7b57f
-- title:
--   Theorem 8.3 — the code $\mathcal C_{\mathrm{HDX}}$ with a doubly-local list-recovery decoder using $\mathbf{NP}^{\mathcal L}$ gates
-- statement:
--   For every $n,\ell\in\mathbb N$, alphabet $\Sigma_0$ and $\epsilon,\delta\in(0,1)$ there is an explicit code $\mathcal C_{\mathrm{HDX}}:\Sigma_0^n\to\Sigma^N$ with $N=\mathrm{poly}(1/\epsilon,1/\delta,\ell)\cdot\widetilde O(n)$ and $\log|\Sigma|=\mathrm{poly}(1/\epsilon,1/\delta,\ell,\log n)\cdot\log|\Sigma_0|$, and a randomized algorithm $\mathcal A$ generating randomized oracle circuits $C_1,\dots,C_L$, $L=O(\ell/\epsilon)$, such that for all input lists $\mathcal L_1,\dots,\mathcal L_N\subseteq\Sigma$ of size $\ell$ and every $f\in\Sigma_0^n$ with
--   $$\Pr_{r\in[N]}\big[\exists g\in\mathcal L_r:\Delta(g,\mathcal C_{\mathrm{HDX}}(f)_r)\le\delta'\big]\ge\epsilon,\qquad\delta'=\frac{\delta^2}{t^2},\ t=\mathrm{polylog}(n),$$
--   we have
--   $$\Pr_{\mathcal A}\Big[\exists i\in[L]:\Pr_{x\in[n],C_i}[C_i(x)=f(x)]\ge1-\delta\Big]\ge\frac34.$$
--   Moreover:
--
--   1. **Decoder complexity.** Each $C_i$ has size $\mathrm{poly}(\log n,\log(\ell/\epsilon),1/\delta,\log|\Sigma_0|)$, $O(\log(\ell/\epsilon)+\log\log(t/\delta))$ $\mathbf{NP}^{\mathcal L}$ oracle gates and one additional oracle gate to $\mathcal L$; $\mathcal A$ generates each $C_i$ in time polynomial in its size.
--   2. **Oracle complexity.** The verifier of the $\mathbf{NP}^{\mathcal L}$ language runs in time $\mathrm{poly}(\log n,\log(\ell/\epsilon),1/\delta,\log|\Sigma_0|)$ and accesses $t$ elements of $\mathcal L$, reading $O\big(\tfrac t\delta\log\tfrac{t\ell}{\delta\epsilon}\big)$ $\Sigma_0$-symbols of each.
--   3. **Encoding complexity.** Each symbol of the encoding is computable in time $\mathrm{poly}(\log n,\ell,1/\epsilon,1/\delta)\cdot\log|\Sigma_0|$ after reading $\mathrm{poly}(\log n,\ell,1/\epsilon,1/\delta)$ locations of the message; each of its $\Sigma_0$-symbols in time $\mathrm{poly}(\log(n\ell|\Sigma_0|/(\epsilon\delta)))$ after reading one location.
--
--   The decoder recovers the message from exponentially small agreement while running in time polylogarithmic in $1/\epsilon$, which no deterministic local decoder can do; the $\mathbf{NP}$ oracle replaces reading whole lists.
--
--   **Formalization Note** $\Sigma_0=[q]$ and $\Sigma=\Sigma_0^b$. The code, $\mathcal A$, the verifier and the two encoders are uniform programs given $(n,\ell,q,\lceil1/\epsilon\rceil,\lceil1/\delta\rceil)$. One constant $K$ serves every $O$, $\mathrm{poly}$ and $\widetilde O$; $\mathrm{poly}(a_1,\dots)=K(a_1+\dots+2)^K$.
--
--   Differences from the source:
--   - reading: logarithms inside O(·) and poly(·) → log₂(·) + 2; reason: the literal log log(t/δ) is negative for t/δ < 2 and log(ℓ/ϵ) vanishes at ℓ/ϵ = 1; the asymptotic convention, as for Theorem 8.6 where the literal reading is false
--   - reading: 'for each of the t queries, the decoder only reads …' → a bound on the distinct Σ₀-symbols the verifier reads of each accessed list element; reason: the t queries are the verifier's (footnote 42)
--   - encoding: alphabet Σ₀; Σ with log|Σ| = poly·log|Σ₀| → Σ₀ = [q]; Σ = Σ₀^b with b ≤ K(1/ϵ + 1/δ + ℓ + log₂ n + 2)^K; reason: a Σ-symbol is a tuple of Σ₀-symbols (the 'Encoding complexity' bullet)
--   - encoding: explicit code; A; verifier; encoders → one program each, uniform in (n, ℓ, q, ⌈1/ϵ⌉, ⌈1/δ⌉); reason: an explicit code is computed by one algorithm for all parameters
--   - encoding: t = polylog(n) → t(n) ≥ 1 with t(n) ≤ K(log₂ n + 2)^K, the same t in δ′, in the number of accessed elements and in the read bound; reason: t = 0 would make δ′ undefined
--   - encoding: input lists ⊆ Σ of size ℓ → lists without repetition of length ℓ, in any order, accessed by queries (r, j, p); reason: a set of size ℓ presented to the oracle in some order
--   - encoding: NP^L gates; one oracle gate to L; size → oracle circuits whose NP^L gates ask ∃w V^L(params, s, w) = 1, with at most one direct list gate; size = number of gates; reason: the paper fixes no circuit model
--   - encoding: A generates each C_i in time polynomial in its size → A's total time ≤ K_a + Σ_i K_a(|C_i| + 1)^{k_a}; reason: the sum over the generated circuits
--   - encoding: n ∈ ℕ; N → n ≥ 1; N ≥ 1 stated; reason: Pr_{x∈[n]} and Pr_{r∈[N]} are undefined for n = 0, N = 0
--   - encoding: time bounds → the base mission's budget (constant and polylogarithmic factors); real powers rounded up; reason: the base mission's convention for the log-cost RAM
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Theorem 8.3, p.66 (pdf p.68)

import Mathlib
import Definitions.Def_TargetedSamplers_Supplement_OracleCircuit

namespace TargetedSamplers.Supplement

/-- Theorem 8.3 (Theorem 1.13, more general version) (Chen, Doron, Ebtehaj, Tell, Targeted Samplers,
STOC 2027 submission, manuscript sha256 599d0a59…, p.66). For every `n, ℓ ∈ ℕ`, alphabet `Σ₀` and
`ϵ, δ ∈ (0, 1)` there is an explicit code `C_HDX : Σ₀ⁿ → Σ^N` with `N = poly(1/ϵ, 1/δ, ℓ) · Õ(n)` and
`log |Σ| = poly(1/ϵ, 1/δ, ℓ, log n) · log |Σ₀|` such that a randomized algorithm `A` generates
randomized oracle circuits `C₁, …, C_L`, `L = O(ℓ/ϵ)`, with: for all input lists `L₁, …, L_N ⊆ Σ` of
size `ℓ` and every `f ∈ Σ₀ⁿ` with `Pr_{r ∈ [N]}[∃ g ∈ L_r : ∆(g, C_HDX(f)_r) ≤ δ′] ≥ ϵ`, where
`δ′ = δ²/t²` for `t = polylog(n)`,
`Pr_A[∃ i ∈ [L] : Pr_{x ∈ [n], C_i}[C_i(x) = f(x)] ≥ 1 − δ] ≥ 3/4`. Moreover:

* *Decoder complexity.* Each `C_i` has size `poly(log n, log(ℓ/ϵ), 1/δ, log |Σ₀|)`,
  `O(log(ℓ/ϵ) + log log(t/δ))` NP^L oracle gates and one additional oracle gate to the lists; `A`
  generates each `C_i` in time polynomial in its size.
* *Oracle complexity.* The verifier of the NP^L language runs in time
  `poly(log n, log(ℓ/ϵ), 1/δ, log |Σ₀|)` and accesses `t` elements of the lists, reading
  `O((t/δ) log(tℓ/(δϵ)))` `Σ₀`-symbols of each.
* *Encoding complexity.* Each symbol of the encoding is computable in time
  `poly(log n, ℓ, 1/ϵ, 1/δ) · log |Σ₀|` after reading `poly(log n, ℓ, 1/ϵ, 1/δ)` locations of the
  message; each of its `Σ₀`-symbols in time `poly(log(nℓ|Σ₀|/(ϵδ)))` after reading one location.

**Formalization Note** `Σ₀ = [q]` and `Σ = Σ₀^b` (tuples of `b` symbols, so `log |Σ| = b log |Σ₀|`);
`∆` is the relative Hamming distance of tuples. The code, `A`, the verifier `V` and the encoders `E`,
`E_in` are uniform: one program each, given `(n, ℓ, q, ⌈1/ϵ⌉, ⌈1/δ⌉)` (`codeParams`). One constant `K`
serves all `O(·)`, `poly(·)` and `Õ(·)`; `poly(a₁, …)` is `K (a₁ + ⋯ + 2)^K` and `Õ(n)` is
`n (log₂ n + 2)^K`. `t(n) ≥ 1` with `t(n) ≤ K (log₂ n + 2)^K`, the same `t` in `δ′`, the verifier's
accesses and its read bound. Lists are given in some order as lists without repetition; the verifier
and the circuits' list gate query `(r, j, p)`, the `p`-th `Σ₀`-symbol of the `j`-th element of `L_r`
(`tupleListOracle`). An NP^L gate answers whether some witness `w` makes `V^L(params, s, w)` accept.
Each logarithm inside `O(·)` is read `log₂(·) + 2`. Positions `x ∈ [n]` and symbols are given in
binary; `n ≥ 1`; `N ≥ 1` is stated (with `N = 0` the agreement hypothesis would never hold). -/
theorem theorem_8_3 : ∃ K : ℝ, 0 < K ∧ ∃ t : ℕ → ℕ,
    (∀ n, 1 ≤ t n ∧ (t n : ℝ) ≤ K * (Real.logb 2 n + 2) ^ K) ∧
    ∃ (N b Lc R : ℕ → ℕ → ℕ → ℝ → ℝ → ℕ)
      (Code : (n ℓ q : ℕ) → (ϵ δ : ℝ) → (Fin n → Fin q) →
        Fin (N n ℓ q ϵ δ) → Fin (b n ℓ q ϵ δ) → Fin q)
      (circs : ℕ → ℕ → ℕ → ℝ → ℝ → List Bool → List OCircuit)
      (A V E Ein : Program) (Ka ka : ℕ),
    ∀ (n ℓ q : ℕ) (ϵ δ : ℝ), 1 ≤ n → 0 < ϵ → ϵ < 1 → 0 < δ → δ < 1 →
      -- parameters
      (1 ≤ N n ℓ q ϵ δ ∧
        (N n ℓ q ϵ δ : ℝ) ≤ K * (1 / ϵ + 1 / δ + ℓ + 2) ^ K * (n * (Real.logb 2 n + 2) ^ K) ∧
        (b n ℓ q ϵ δ : ℝ) ≤ K * (1 / ϵ + 1 / δ + ℓ + Real.logb 2 n + 2) ^ K ∧
        (Lc n ℓ q ϵ δ : ℝ) ≤ K * (ℓ / ϵ)) ∧
      -- the generator `A` and decoder complexity
      (∀ ρ : List Bool, ρ.length = R n ℓ q ϵ δ →
        A.RunsIn ⟨encInput (codeParams n ℓ q ϵ δ) [], ρ, [], noOracle⟩
          (Ka + ((circs n ℓ q ϵ δ ρ).map fun C => Ka * (C.size + 1) ^ ka).sum)
          (some (encodeCircuits (circs n ℓ q ϵ δ ρ))) ∧
        (circs n ℓ q ϵ δ ρ).length ≤ Lc n ℓ q ϵ δ ∧
        ∀ C ∈ circs n ℓ q ϵ δ ρ, C.inLen = Nat.clog 2 n ∧
          (C.size : ℝ) ≤ K * (Real.logb 2 n + Real.logb 2 (ℓ / ϵ) + 1 / δ + Real.logb 2 q + 2) ^ K ∧
          (C.numOracle : ℝ) ≤
            K * (Real.logb 2 (ℓ / ϵ) + Real.logb 2 (Real.logb 2 (t n / δ) + 2) + 2) ∧
          C.numListQ ≤ 1) ∧
      -- oracle complexity of the NP^L verifier
      (∀ (L : Fin (N n ℓ q ϵ δ) → List (Fin (b n ℓ q ϵ δ) → Fin q)) (s w : List Bool),
        (∃ bit : Bool, V.RunsIn ⟨encInput (codeParams n ℓ q ϵ δ) [s, w], [], [], tupleListOracle L⟩
          ⌈K * (Real.logb 2 n + Real.logb 2 (ℓ / ϵ) + 1 / δ + Real.logb 2 q + 2) ^ K⌉₊ (some [bit])) ∧
        (tupleQueryElems (V.queriesAsked
          ⟨encInput (codeParams n ℓ q ϵ δ) [s, w], [], [], tupleListOracle L⟩)).length ≤ t n ∧
        ∀ π : List ℕ, (tupleQueryReads (V.queriesAsked
          ⟨encInput (codeParams n ℓ q ϵ δ) [s, w], [], [], tupleListOracle L⟩) π : ℝ) ≤
            K * (t n / δ) * (Real.logb 2 (t n * ℓ / (δ * ϵ)) + 2)) ∧
      -- list recovery
      (∀ (L : Fin (N n ℓ q ϵ δ) → List (Fin (b n ℓ q ϵ δ) → Fin q)) (f : Fin n → Fin q),
        (∀ r, (L r).length = ℓ ∧ (L r).Nodup) →
        ϵ ≤ fracFin (N n ℓ q ϵ δ) (fun r => ∃ g ∈ L r,
          relHamming g (Code n ℓ q ϵ δ f r) ≤ δ ^ 2 / (t n : ℝ) ^ 2) →
        3 / 4 ≤ coinProb (R n ℓ q ϵ δ) (fun ρ => ∃ C ∈ circs n ℓ q ϵ δ ρ,
          1 - δ ≤ circSuccess C (npLang V (codeParams n ℓ q ϵ δ) (tupleListOracle L))
            (listGateAnswer (tupleListOracle L) q) f)) ∧
      -- encoding complexity
      (∀ (f : Fin n → Fin q) (r : Fin (N n ℓ q ϵ δ)),
        E.RunsIn ⟨encInput (codeParams n ℓ q ϵ δ ++ [r.val]) [], [], [], msgOracle f⟩
          ⌈K * (Real.logb 2 n + ℓ + 1 / ϵ + 1 / δ + 2) ^ K * (Real.logb 2 q + 2)⌉₊
          (some ((List.ofFn fun u => bitsFixed (Nat.clog 2 q) (Code n ℓ q ϵ δ f r u)).flatten)) ∧
        ((E.queriesAsked ⟨encInput (codeParams n ℓ q ϵ δ ++ [r.val]) [], [], [], msgOracle f⟩).dedup.length
          : ℝ) ≤ K * (Real.logb 2 n + ℓ + 1 / ϵ + 1 / δ + 2) ^ K) ∧
      (∀ (f : Fin n → Fin q) (r : Fin (N n ℓ q ϵ δ)) (u : Fin (b n ℓ q ϵ δ)),
        Ein.RunsIn ⟨encInput (codeParams n ℓ q ϵ δ ++ [r.val, u.val]) [], [], [], msgOracle f⟩
          ⌈K * (Real.logb 2 (n * ℓ * q / (ϵ * δ)) + 2) ^ K⌉₊
          (some (bitsFixed (Nat.clog 2 q) (Code n ℓ q ϵ δ f r u))) ∧
        (Ein.queriesAsked
          ⟨encInput (codeParams n ℓ q ϵ δ ++ [r.val, u.val]) [], [], [], msgOracle f⟩).dedup.length ≤ 1) := by sorry

end TargetedSamplers.Supplement
