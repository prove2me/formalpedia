-- Prove2me | Theorems.Thm_QuantumKtSoI_Supplement_theorem_8_3
-- name    : QuantumKtSoI.Supplement.theorem_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:47:02.591158+00:00
-- url     : https://prove2.me/theorems/2a7cc751-afe0-408f-bcfe-a20f7e08a614
-- title:
--   Theorem 8.3, p.113 — a quantum-secure one-way function gives a fixed classical sampler with defect above $C\log(2N_m+2)$ with probability $1-\mathrm{negl}$
-- statement:
--   Suppose $f_m:\{0,1\}^m\to\{0,1\}^*$ is a quantum-secure classical one-way function (Definition 8.1). Then there are a fixed classical polynomial-time sampler $S$, outputting on $1^N$ a pair $(X,Y)\in\{0,1\}^N\times\{0,1\}^N$ for every $N$, and an increasing polynomial $N_m=A_0(m+2)^D$ with fixed integers $A_0,D\ge1$, such that:
--
--   1. for every fixed constant $C\ge0$ a negligible function $\varepsilon_C$ satisfies, for all $m\ge1$,
--   $$\Pr_{(X,Y)\sim S(1^{N_m})}\big[\mathrm{qKt}(Y|X)+\mathrm{qKt}(X)-\mathrm{qKt}(\langle X,Y\rangle)>C\log(2N_m+2)\big]\ge1-\varepsilon_C(m),$$
--   and $\varepsilon_C$ is also negligible as a function of $N_m$;
--   2. $S$ on input $1^{N_m}$ draws a uniform seed $Z\in\{0,1\}^m$ and outputs $Y=Z0^{N_m-m}$ and an encoding $X$ of $m$ and $f_m(Z)$;
--   3. with $F_y=|f_m^{-1}(y)|$, for every fixed constant $B\ge0$ the probability $\Pr_Z[\mathrm{qKt}(Y|X)\le\log F_{f_m(Z)}+B\log(m+2)]$ is negligible in $m$;
--   4. the set of lengths $N_m$ is decidable in time polynomial in $N$.
--
--   The sampler and the lengths do not depend on $C$ or $B$.
--
--   This is the classical-sampling failure of symmetry with probability close to one, under a cryptographic assumption.
--
--   **Formalization Note** Negligible is the published `QAdvFew.PoQOracle.Negligible`; "negligible as a function of $N_m$" is: for every $c>0$, eventually $\varepsilon_C(m)\le N_m^{-c}$.
--
--   Differences from the source:
--   - generalization: the glue routines are fixed once and for all by their p.24 properties → every admissible glue routine set G (hypothesis G.Admissible); descriptions, P_e and qKt are those of G; reason: the proofs use only the p.24 properties and the paper's routines are one admissible set; same as the published base items
--   - reading: a classical polynomial-time sampler (p.51: a machine whose only qubit operations are fair-coin draws) → the published PolySampler: a §2.1 probabilistic Turing machine with an all-branch polynomial deadline and 2N output bits on 1^N; reason: the reading of the published goal of the base mission (same families are sampled)
--   - reading: "draws a uniform seed Z and outputs Y = Z0^{N_m−m} and an encoding X of m and f_m(Z)" → an injective Enc(m, y) exists such that for every z ∈ {0,1}^m the output is (Enc(m, f_m(z)), z0^{N_m−m}) with probability 2^{−m}; reason: the output law of such a sampler; the paper names no particular encoding
--   - reading: the set of lengths N_m is decidable in time polynomial in N → a deterministic coded machine on input b(N) outputs the indicator of {N_m : m ≥ 1} within c(N+2)^k steps; reason: time polynomial in the value N; no input format is named
--   - encoding: negligible: ν(n) < n^{−c} for all large n, for every c > 0 (p.14) → the published QAdvFew.PoQOracle.Negligible: nonnegative and eventually ≤ n^{−c} for every c > 0; reason: the two conditions are equivalent (quantified over every c)
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem 8.3, p.113; Definition 8.1, p.111

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt
import Definitions.Def_QuantumKtSoI_PolySampler
import Definitions.Def_QuantumKtSoI_Supplement_QSOWF

open Classical

namespace QuantumKtSoI.Supplement

/-- **Theorem 8.3** (Classical sampling from quantum-secure one-way functions; Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…, p.113). Suppose
`f_m : {0,1}^m → {0,1}*` is a quantum-secure classical one-way function (Definition 8.1, input
length `m`). Then there are a fixed classical polynomial-time sampler `S` and an increasing
polynomial `N_m = A₀(m+2)^D` (fixed integers `A₀, D ≥ 1`) such that `S(1^N)` outputs a pair
`(X, Y) ∈ {0,1}^N × {0,1}^N` for every `N`, and
1. for every constant `C ≥ 0` a negligible `ε_C` satisfies
   `Pr_{(X,Y)∼S(1^{N_m})}[qKt(Y|X) + qKt(X) − qKt(⟨X,Y⟩) > C log(2N_m+2)] ≥ 1 − ε_C(m)` for all
   `m ≥ 1`, and `ε_C` is also negligible as a function of `N_m`;
2. `S(1^{N_m})` draws a uniform seed `Z ∈ {0,1}^m` and outputs `Y = Z0^{N_m−m}` and an encoding `X`
   of `m` and `f_m(Z)`;
3. with `F_y = |f_m^{−1}(y)|`, for every constant `B ≥ 0` the probability
   `Pr_Z[qKt(Y|X) ≤ log F_{f_m(Z)} + B log(m+2)]` is negligible in `m`;
4. the set of lengths `{N_m}` is decidable in time polynomial in `N`.
The sampler and the lengths do not depend on `C` or `B`.

**Formalization Note** `S` is a published `PolySampler` (§2.1 probabilistic Turing machine with an
all-branch polynomial deadline whose `2N`-bit output is `(X, Y)`); `S.prob` is the probability over
its coin sequence. "An encoding of `m` and `f_m(Z)`" is an injective `Enc(m, y)`, and "draws a uniform
seed `Z` and outputs …" is: for every `z ∈ {0,1}^m` the output is `(Enc(m, f_m(z)), z0^{N_m−m})` with
probability `2^{−m}`. Negligible is the published `QAdvFew.PoQOracle.Negligible` (the paper's
p.14 notion). "Negligible as a function of `N_m`" is: for every `c > 0`, eventually
`ε_C(m) ≤ N_m^{−c}`. Decidability of `{N_m}` is by a deterministic machine on input `b(N)` within
`c(N+2)^k` steps (time polynomial in the value `N`). `G` is any admissible glue routine set. -/
theorem theorem_8_3 (G : GlueRoutines) (hG : G.Admissible) (f : List Bool → List Bool)
    (hf : QuantumSecureOWF f) :
    ∃ S : PolySampler, ∃ A₀ D : ℕ, 1 ≤ A₀ ∧ 1 ≤ D ∧
      (∀ C : ℝ, 0 ≤ C → ∃ ε : ℕ → ℝ, QAdvFew.PoQOracle.Negligible ε ∧
        (∀ m : ℕ, 1 ≤ m → 1 - ε m ≤
          S.prob (A₀ * (m + 2) ^ D) fun X Y =>
            C * Real.logb 2 (2 * ((A₀ * (m + 2) ^ D : ℕ) : ℝ) + 2) < (defect G X Y : ℝ)) ∧
        ∀ c : ℝ, 0 < c → ∃ m₀ : ℕ, ∀ m ≥ m₀, ε m ≤ ((A₀ * (m + 2) ^ D : ℕ) : ℝ) ^ (-c)) ∧
      (∃ Enc : ℕ → List Bool → List Bool,
        (∀ m m' : ℕ, ∀ y y' : List Bool, Enc m y = Enc m' y' → m = m' ∧ y = y') ∧
        (∀ m : ℕ, 1 ≤ m → ∀ z : Fin m → Bool,
          S.prob (A₀ * (m + 2) ^ D) (fun X Y => X = Enc m (f (List.ofFn z)) ∧
            Y = List.ofFn z ++ List.replicate (A₀ * (m + 2) ^ D - m) false) = 1 / 2 ^ m) ∧
        ∀ B : ℝ, 0 ≤ B → QAdvFew.PoQOracle.Negligible fun m =>
          ((Finset.univ.filter fun z : Fin m → Bool =>
              (qKt G (List.ofFn z ++ List.replicate (A₀ * (m + 2) ^ D - m) false)
                  (Enc m (f (List.ofFn z))) : ℝ) ≤
                Real.logb 2 ((Finset.univ.filter fun z' : Fin m → Bool =>
                    f (List.ofFn z') = f (List.ofFn z)).card : ℝ) +
                  B * Real.logb 2 ((m : ℝ) + 2)).card : ℝ) / 2 ^ m) ∧
      ∃ F : CodedMachine, F.Valid ∧ F.GateFree ∧ ∃ c k : ℕ, ∀ N : ℕ,
        F.toMachine.HaltsWithin (bin N) (c * (N + 2) ^ k) ∧
          F.toMachine.outputProb (bin N) (c * (N + 2) ^ k)
            [decide (∃ m : ℕ, 1 ≤ m ∧ N = A₀ * (m + 2) ^ D)] = 1 := by sorry

end QuantumKtSoI.Supplement
