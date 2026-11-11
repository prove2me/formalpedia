-- Prove2me | Theorems.Thm_QNatProofs_theorem_3_3
-- name    : QNatProofs.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:06:13.907511+00:00
-- url     : https://prove2.me/theorems/5e4b2bbe-da12-48be-9e42-931e83545922
-- title:
--   Theorem 3.3 — PRF replacement
-- statement:
--   Let samplers $\mathrm{Samp}_{n,R,T}:\{0,1\}^R\to\{0,1\}^\ell$ and thresholds $\gamma_{n,R,T}>0$ be given such that one classical machine computes $\mathrm{Samp}_{n,R,T}(\omega)$ in time polynomial in $N+R+T$, $N=2^n$, and $\gamma^2_{n,R,T}$ is rational and computed by one machine in time polynomial in $N+R+T$. Then there is a fixed polynomial $P$ such that the following holds for all $n,R,T$.
--
--   Let $F=\{F_k:\{0,1\}^n\to\{0,1\}^R\}_k$ be a keyed family, and let $D_F$ and $D_{\mathrm{rf}}$ be the laws of $|\psi_{F_k,\gamma}\rangle$ for a uniform key and of $|\psi_{H,\gamma}\rangle$ for a uniformly random function, with $\mathrm{Samp}=\mathrm{Samp}_{n,R,T}$, $\gamma=\gamma_{n,R,T}$. If every classical oracle distinguisher running in time $t_{\mathrm{PRF}}$ has advantage at most $\varepsilon_{\mathrm{PRF}}$ against $F$, then every classical distinguisher $A$ running in time $t_A$ on amplitude lists with $t_A+P(N,R,T)\le t_{\mathrm{PRF}}$ satisfies
--   $$
--   \Big|\Pr_{\psi\leftarrow D_F}[A(\mathrm{al}_T(\psi))=1]-\Pr_{\psi\leftarrow D_{\mathrm{rf}}}[A(\mathrm{al}_T(\psi))=1]\Big|\le\varepsilon_{\mathrm{PRF}}.
--   $$
--
--   This is the computational half: a distinguisher for the amplitude lists yields a PRF distinguisher with an additive $2^{O(n)}$ overhead.
--
--   Differences from the source:
--   - generalization: Samp classically computable in time poly(N, R); γ² rational and computable in time poly(N, R, T) → families Samp_{n,R,T} and γ_{n,R,T} (which may depend on n, R, T), each computed by one FinTM2 machine from the unary codes of n, R, T within p(2^n + R + T) steps; γ² output as a reduced fraction; reason: a weaker hypothesis on the sampler (it may depend on T and use time polynomial in T); a fixed Samp and γ are a constant family
--   - generalization: threshold γ ∈ (0, 1] of (6) → γ_{n,R,T} > 0; reason: the bound γ ≤ 1 is not used
--   - encoding: a fixed polynomial P(N, R, T) → one P : ℕ[X] evaluated at 2^n + R + T, chosen after the machines and before n, R, T, F, t_PRF, ε_PRF and A; reason: a polynomial in (N, R, T) is bounded by a polynomial in their sum
--   - encoding: classical oracle distinguishers running in time t_PRF; a classical distinguisher A running in time t_A → OracleAlg (uniform, probabilistic, adaptive) on any input, time bound over every oracle {0,1}^n → {0,1}^R of the game and every coin string; A a query-free OracleAlg whose bound holds on every string of the length T·2^{n+1} of an amplitude list; reason: an input plays the role of constants hard-wired into an algorithm; A receives no oracle
--   - encoding: probabilities over ψ and the coins of A → alProb: Σ_s D{al_T = s}·Pr_coins[A(s) = 1]; reason: al_T takes finitely many values
--   - reading: al_T(ψ): polar coordinates written to T fractional bits → QNatProofs.al: basis strings in increasing binary order, r-bits then θ-bits, truncation ⌊2^T r⌋ capped at 2^T−1 (so r = 1 is written 1⋯1), θ = arg/(2π) mod 1 with θ(0) = 0; reason: the printed codomain {0,1}^{2T·2^n} forces the cap; the order and θ(0) are unspecified on p.8
--   - encoding: binary encoding of the polar coordinates (r, θ) ∈ [0,1)² (Definition 3.1) → two q-bit binary fractions, most significant bit first (Sampler R q); reason: any finite binary-fraction encoding becomes one of this form by padding with zeros, which changes no encoded complex number
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), Theorem 3.3, p.15; proof p.15–16

import Mathlib
import Definitions.Def_QNatProofs_pralFamily

set_option autoImplicit false

namespace QNatProofs

open QAlgorithms QAlgorithms.Complexity Polynomial

/-- **Theorem 3.3 (PRF replacement)** (Li, Parham, *Natural proofs for quantum state preparation
lower bounds*, arXiv:2610.06826 (held copy sha256 b604fa11…), p.15; proof p.15–16): "Let
`F = {F_k : {0,1}ⁿ → {0,1}^R}_k` be a function family, and let `D_F` and `D_rf` denote the state
distributions obtained from a uniformly random key and a uniformly random function respectively,
using sampler `Samp : {0,1}^R → {0,1}^ℓ` and threshold `γ`. Let `T` be the truncation precision,
and write `N = 2ⁿ`. Assume that `Samp` is classically computable in time `poly(N, R)` and that `γ²`
is rational and computable in time `poly(N, R, T)`. There is a fixed polynomial `P` such that the
following holds. If `F` is secure against classical oracle distinguishers running in time `t_PRF`,
with distinguishing advantage at most `ε_PRF`, then every classical distinguisher `A` running in
time `t_A` with `t_A + P(N, R, T) ≤ t_PRF` satisfies
`|Pr_{ψ←D_F}[A(al_T(ψ)) = 1] − Pr_{ψ←D_rf}[A(al_T(ψ)) = 1]| ≤ ε_PRF`."

**Formalization Note** The samplers and thresholds form families `samp n R T`, `γ n R T` indexed
by `(n, R, T)`; one machine computes each family from the unary codes of `n, R, T` (and the tape)
within `p(2ⁿ + R + T)` steps, and the threshold machine outputs `γ²` as a reduced fraction. The
polynomial `P` is chosen after these machines and before `n, R, T`, the family `F`, `t_PRF`,
`ε_PRF` and `A`. Oracle distinguishers are `OracleAlg`s on any input (an input plays the role of
constants hard-wired into the algorithm), with running time bounded against every oracle
`{0,1}ⁿ → {0,1}^R`; `A` is a query-free `OracleAlg` (a probabilistic classical algorithm, so the
oracle in its time bound is immaterial) whose time bound holds on every string of the length of an
amplitude list. -/
theorem theorem_3_3 (ℓ : ℕ → ℕ → ℕ → ℕ) (samp : (n R T : ℕ) → Sampler R (ℓ n R T))
    (γ : ℕ → ℕ → ℕ → ℝ) (hγpos : ∀ n R T : ℕ, 0 < γ n R T)
    (hsamp : ∃ (M : Turing.TM2ComputableAux Bool Bool) (p : ℕ[X]), ∀ (n R T : ℕ) (ω : Fin R → Bool),
      MachineComputesIn M (encNat n ++ encNat R ++ encNat T ++ List.ofFn ω)
        (List.ofFn (samp n R T ω).1 ++ List.ofFn (samp n R T ω).2) (p.eval (2 ^ n + R + T)))
    (hγ : ∃ (M : Turing.TM2ComputableAux Bool Bool) (p : ℕ[X]), ∀ n R T : ℕ, ∃ r : ℚ,
      γ n R T ^ 2 = r ∧
      MachineComputesIn M (encNat n ++ encNat R ++ encNat T)
        (PPADSIS.SubexpSIS.encInt r.num ++ PPADSIS.SubexpSIS.encNat r.den) (p.eval (2 ^ n + R + T))) :
    ∃ P : ℕ[X], ∀ (n R T : ℕ) (κ : Type) [Fintype κ] [Nonempty κ]
      (F : κ → Qubits n → Fin R → Bool) (tPRF εPRF : ℝ),
      (∀ (B : OracleAlg) (inp : List Bool), B.TimeBounded n R inp tPRF → oracleAdv B inp F ≤ εPRF) →
      ∀ (A : OracleAlg) (tA : ℝ), A.IsQueryFree →
        (∀ s : List Bool, s.length = T * 2 ^ (n + 1) → A.TimeBounded 0 0 s tA) →
        tA + ((P.eval (2 ^ n + R + T) : ℕ) : ℝ) ≤ tPRF →
        |alProb (DF (γ n R T) (samp n R T) F) T (fun s => A.accept (fun _ => []) s) -
          alProb (Drf n (γ n R T) (samp n R T)) T (fun s => A.accept (fun _ => []) s)| ≤
          εPRF := by sorry

end QNatProofs
