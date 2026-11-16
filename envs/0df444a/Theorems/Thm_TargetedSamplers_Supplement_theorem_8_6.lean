-- Prove2me | Theorems.Thm_TargetedSamplers_Supplement_theorem_8_6
-- name    : TargetedSamplers.Supplement.theorem_8_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:17:34.269132+00:00
-- url     : https://prove2.me/theorems/cc75891d-682c-41a1-9081-cd599fe19485
-- title:
--   Theorem 8.6 — locally list-recoverable concatenated code with $\Sigma_2^{\mathcal L}$-gate decoders (corrected: logarithms read $\log_2(\cdot)+2$)
-- statement:
--   For any $n,\ell\in\mathbb N$, alphabet $\Sigma_0$ and $\epsilon,\delta\in(0,1)$ there is a code $\mathcal C:\Sigma_0^n\to\Sigma^{N'}$ that is $\delta$-approximate $\ell$-input $(\epsilon,L)$ locally list recoverable with $\log|\Sigma|=O(\log(\ell/\epsilon))$,
--   $$L=O\Big(\frac\ell\epsilon\log^2\frac1\epsilon\Big),\qquad N'=\Big(\frac{\ell}{\epsilon\delta}\log(n)\log|\Sigma_0|\Big)^{O(\log(\ell/\epsilon))}\cdot n.$$
--   That is, a randomized algorithm $\mathcal A$ generates randomized oracle circuits $C_1,\dots,C_L$ such that for all input lists $\{\mathcal L_z\}_{z\in[N']}$, $\mathcal L_z\subseteq\Sigma$ of size at most $\ell$, and every $f\in\Sigma_0^n$ with $\Pr_{z\in[N']}[\mathcal C(f)_z\in\mathcal L_z]\ge\epsilon$,
--   $$\Pr_{\mathcal A}\Big[\exists i\in[L]:\Pr_{x\in[n],C_i}\big[C_i^{\mathcal L}(x)=f(x)\big]\ge1-\delta\Big]\ge\frac34.$$
--   Moreover:
--
--   1. **Decoder complexity.** Each $C_i$ has size $\mathrm{poly}(\log n,\log(\ell/\epsilon),1/\delta,\log|\Sigma_0|)$ and $O(\log(\ell/\epsilon)+\log|\Sigma_0|+\log\log((\log n)/\delta))$ $\Sigma_2^{\mathcal L}$ oracle gates; $\mathcal A$ generates each circuit in time polynomial in its size.
--   2. **Oracle complexity.** The verifier of the $\Sigma_2^{\mathcal L}$ language runs in time $\mathrm{poly}(\log n,\log(\ell/\epsilon),1/\delta,\log|\Sigma_0|)$ and makes $O(1)$ queries to $\mathcal L$.
--   3. **Encoding complexity.** Each output symbol is computable in time $\mathrm{poly}(\log n,\log(\ell/\epsilon),1/\delta,\log|\Sigma_0|)$.
--
--   This is the code used for hardness amplification towards the hypotheses of the targeted-sampler constructions: list recovery from exponentially small agreement with decoders of polylogarithmic size.
--
--   **Formalization Note** $\Sigma_0=[q]$ and $\Sigma=\{0,1\}^s$. The code, $\mathcal A$, the verifier and the encoder are uniform programs given $(n,\ell,q,\lceil1/\epsilon\rceil,\lceil1/\delta\rceil)$. One constant $K$ serves every $O$ and $\mathrm{poly}$, with $\mathrm{poly}(a_1,\dots)=K(a_1+\dots+2)^K$.
--
--   Differences from the source:
--   - correction: logarithms in L = O((ℓ/ϵ)·log²(1/ϵ)), in N′ and in the gate count → log₂(·) + 2; reason: with any fixed constant the printed L is below 1 at ϵ = 0.99 (log(1/ϵ) → 0), so no circuit would be generated although the true codeword in the lists meets the agreement hypothesis; at n = 1 the printed N′ is 0
--   - reading: 'the code C above' (the proof's C_HDX ∘ C_in) → there exists a code with every listed property; reason: as in Theorem 8.3's 'there exists an explicit code'; the construction is the proof's business
--   - encoding: alphabet Σ₀; Σ = {0,1}^s with log|Σ| = O(log(ℓ/ϵ)) → Σ₀ = [q]; Σ = [2^s] with s ≤ K(log₂(ℓ/ϵ) + 2); reason: same instances
--   - encoding: code; A; verifier; encoder → one program each, uniform in (n, ℓ, q, ⌈1/ϵ⌉, ⌈1/δ⌉); reason: an explicit code is computed by one algorithm for all parameters
--   - encoding: input lists L_z ⊆ Σ of size at most ℓ → lists without repetition of length at most ℓ, in any order, accessed by queries (z, j); reason: a set presented to the oracle in some order
--   - reading: C_i^L with O(·) Σ₂^L oracle gates; size → oracle circuits whose oracle gates ask ∃w₁ ∀w₂ V^L(params, s, w₁, w₂) = 1, with no other oracle gate (no direct list gate); size = number of gates; reason: the page lists only Σ₂^L gates (unlike Theorem 8.3, which names its extra list gate), and the proof (p.76) recovers the output symbol through the Σ₂ oracle with O(log ℓ′ + log|Σ₀|) oracle gates
--   - encoding: A generates each circuit in time polynomial in its size → A's total time ≤ K_a + Σ_i K_a(|C_i| + 1)^{k_a}; reason: the sum over the generated circuits
--   - encoding: n, ℓ ∈ ℕ; N′ → n ≥ 1, ℓ ≥ 1; N′ ≥ 1 stated; reason: Pr_{x∈[n]} is undefined at n = 0, log(ℓ/ϵ) at ℓ = 0, and Pr_{z∈[N′]} at N′ = 0
--   - encoding: time bounds → the base mission's budget (constant and polylogarithmic factors); real powers rounded up; reason: the base mission's convention for the log-cost RAM
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Theorem 8.6, pp.74–75 (pdf pp.76–77)

import Mathlib
import Definitions.Def_TargetedSamplers_Supplement_OracleCircuit

namespace TargetedSamplers.Supplement

/-- Theorem 8.6 (the general case of Corollary 8.2 that allows list-recovery) (Chen, Doron, Ebtehaj,
Tell, Targeted Samplers, STOC 2027 submission, manuscript sha256 599d0a59…, pp.74–75). For any
`n, ℓ ∈ ℕ`, alphabet `Σ₀` and `ϵ, δ ∈ (0, 1)`, the code `C : Σ₀ⁿ → Σ^{N′}` is `δ`-approximate
`ℓ`-input `(ϵ, L)` locally list recoverable with `log |Σ| = O(log(ℓ/ϵ))`,
`L = O((ℓ/ϵ) · log²(1/ϵ))` and `N′ = ((ℓ/(ϵδ)) · log(n) log |Σ₀|)^{O(log(ℓ/ϵ))} · n`: a randomized
algorithm `A` generates randomized oracle circuits `C₁, …, C_L` such that for all input lists
`{L_z}_{z ∈ [N′]}`, `L_z ⊆ Σ` of size at most `ℓ`, and every `f ∈ Σ₀ⁿ` with
`Pr_{z ∈ [N′]}[C(f)_z ∈ L_z] ≥ ϵ`, `Pr_A[∃ i ∈ [L] : Pr_{x ∈ [n], C_i}[C_i^L(x) = f(x)] ≥ 1 − δ] ≥ 3/4`.
Moreover:

* *Decoder complexity.* Each `C_i` has size `poly(log n, log(ℓ/ϵ), 1/δ, log |Σ₀|)` and
  `O(log(ℓ/ϵ) + log |Σ₀| + log log((log n)/δ))` Σ₂^L oracle gates; `A` generates each circuit in time
  polynomial in its size.
* *Oracle complexity.* The verifier of the Σ₂^L language runs in time
  `poly(log n, log(ℓ/ϵ), 1/δ, log |Σ₀|)` and makes `O(1)` queries to the lists.
* *Encoding complexity.* Each output symbol of `C` is computable in time
  `poly(log n, log(ℓ/ϵ), 1/δ, log |Σ₀|)`.

**Formalization Note** "The code `C` above" is the proof's construction `C_HDX ∘ C_in`; the theorem is
stated as the existence of a code with every listed property, like Theorem 8.3's "there exists an
explicit code". `Σ₀ = [q]`, `Σ = {0,1}^s` (p.74) with `s = log |Σ|`. The code, `A`, the verifier `V`
and the encoder `E` are uniform: one program each, given `(n, ℓ, q, ⌈1/ϵ⌉, ⌈1/δ⌉)` (`codeParams`).
One constant `K` serves all `O(·)` and `poly(·)`; `poly(a₁, …)` is `K (a₁ + ⋯ + 2)^K`; every
logarithm is read `log₂(·) + 2` (at `n = 1` the printed `N′` bound is `0`, and at `ϵ = 0.99` the
printed `L` is below `1`, though a code and a decoder exist). Lists are lists without repetition of
length at most `ℓ`, in some order; the verifier queries `(z, j)`, the `j`-th element of `L_z`
(`symListOracle`), and a Σ₂^L gate answers whether some `w₁` makes `V^L(params, s, w₁, w₂)` accept
for every `w₂`. The circuits have no other oracle gates. `n ≥ 1` and `ℓ ≥ 1` (at `ℓ = 0`, `log(ℓ/ϵ)` is undefined); `N′ ≥ 1` is stated (with `N′ = 0`
the agreement hypothesis would never hold). -/
theorem theorem_8_6 : ∃ K : ℝ, 0 < K ∧
    ∃ (N' s Lc R : ℕ → ℕ → ℕ → ℝ → ℝ → ℕ)
      (Code : (n ℓ q : ℕ) → (ϵ δ : ℝ) → (Fin n → Fin q) →
        Fin (N' n ℓ q ϵ δ) → Fin (2 ^ s n ℓ q ϵ δ))
      (circs : ℕ → ℕ → ℕ → ℝ → ℝ → List Bool → List OCircuit)
      (A V E : Program) (Ka ka : ℕ),
    ∀ (n ℓ q : ℕ) (ϵ δ : ℝ), 1 ≤ n → 1 ≤ ℓ → 0 < ϵ → ϵ < 1 → 0 < δ → δ < 1 →
      -- parameters
      ((s n ℓ q ϵ δ : ℝ) ≤ K * (Real.logb 2 (ℓ / ϵ) + 2) ∧
        (Lc n ℓ q ϵ δ : ℝ) ≤ K * (ℓ / ϵ) * (Real.logb 2 (1 / ϵ) + 2) ^ 2 ∧
        1 ≤ N' n ℓ q ϵ δ ∧
        (N' n ℓ q ϵ δ : ℝ) ≤
          ((ℓ / (ϵ * δ)) * (Real.logb 2 n + 2) * (Real.logb 2 q + 2)) ^
            (K * (Real.logb 2 (ℓ / ϵ) + 2)) * n) ∧
      -- the generator `A` and decoder complexity
      (∀ ρ : List Bool, ρ.length = R n ℓ q ϵ δ →
        A.RunsIn ⟨encInput (codeParams n ℓ q ϵ δ) [], ρ, [], noOracle⟩
          (Ka + ((circs n ℓ q ϵ δ ρ).map fun C => Ka * (C.size + 1) ^ ka).sum)
          (some (encodeCircuits (circs n ℓ q ϵ δ ρ))) ∧
        (circs n ℓ q ϵ δ ρ).length ≤ Lc n ℓ q ϵ δ ∧
        ∀ C ∈ circs n ℓ q ϵ δ ρ, C.inLen = Nat.clog 2 n ∧
          (C.size : ℝ) ≤ K * (Real.logb 2 n + Real.logb 2 (ℓ / ϵ) + 1 / δ + Real.logb 2 q + 2) ^ K ∧
          (C.numOracle : ℝ) ≤ K * (Real.logb 2 (ℓ / ϵ) + Real.logb 2 q +
            Real.logb 2 (Real.logb 2 ((Real.logb 2 n + 2) / δ) + 2) + 2) ∧
          C.numListQ = 0) ∧
      -- oracle complexity of the Σ₂^L verifier
      (∀ (L : Fin (N' n ℓ q ϵ δ) → List (Fin (2 ^ s n ℓ q ϵ δ))) (s' w₁ w₂ : List Bool),
        (∃ bit : Bool, V.RunsIn
          ⟨encInput (codeParams n ℓ q ϵ δ) [s', w₁, w₂], [], [], symListOracle L⟩
          ⌈K * (Real.logb 2 n + Real.logb 2 (ℓ / ϵ) + 1 / δ + Real.logb 2 q + 2) ^ K⌉₊ (some [bit])) ∧
        ((V.queriesAsked ⟨encInput (codeParams n ℓ q ϵ δ) [s', w₁, w₂], [], [], symListOracle L⟩).length
          : ℝ) ≤ K) ∧
      -- list recovery
      (∀ (L : Fin (N' n ℓ q ϵ δ) → List (Fin (2 ^ s n ℓ q ϵ δ))) (f : Fin n → Fin q),
        (∀ z, (L z).length ≤ ℓ ∧ (L z).Nodup) →
        ϵ ≤ fracFin (N' n ℓ q ϵ δ) (fun z => Code n ℓ q ϵ δ f z ∈ L z) →
        3 / 4 ≤ coinProb (R n ℓ q ϵ δ) (fun ρ => ∃ C ∈ circs n ℓ q ϵ δ ρ,
          1 - δ ≤ circSuccess C (sigma2Lang V (codeParams n ℓ q ϵ δ) (symListOracle L))
            (listGateAnswer (symListOracle L) (2 ^ s n ℓ q ϵ δ)) f)) ∧
      -- encoding complexity
      (∀ (f : Fin n → Fin q) (z : Fin (N' n ℓ q ϵ δ)),
        E.RunsIn ⟨encInput (codeParams n ℓ q ϵ δ ++ [z.val]) [], [], [], msgOracle f⟩
          ⌈K * (Real.logb 2 n + Real.logb 2 (ℓ / ϵ) + 1 / δ + Real.logb 2 q + 2) ^ K⌉₊
          (some (bitsFixed (s n ℓ q ϵ δ) (Code n ℓ q ϵ δ f z)))) := by sorry

end TargetedSamplers.Supplement
