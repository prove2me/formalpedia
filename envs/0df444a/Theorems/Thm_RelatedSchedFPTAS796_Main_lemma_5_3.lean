-- Prove2me | Theorems.Thm_RelatedSchedFPTAS796_Main_lemma_5_3
-- name    : RelatedSchedFPTAS796.Main.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:14:44.226247+00:00
-- url     : https://prove2.me/theorems/24ea3989-8a09-4b84-a17b-d5e6f821f6ed
-- title:
--   Lemma 5.3 — extending a dense certificate to an $\tilde O(\kappa)$-approximation of $\mathcal S(J,[\kappa/\varepsilon,(2d+1)\kappa/(2d\varepsilon)))$
-- statement:
--   Let $\varepsilon=2^{-\ell}$, $d\ge1$, and let $J$ be a multiset of integers in $[1/\varepsilon,2/\varepsilon)$ with
--   $$\Sigma(J)\ \ge\ \frac{d+1}{d}\sum_{j=1}^d\frac{\kappa_j}{\varepsilon},$$
--   where $1\le\kappa_1\le\dots\le\kappa_d=O(1/\varepsilon)$ are the parameters of the partial-profile instance. Given a dense certificate $(J',S')$ for $J$ (Definition 5.2, with error $\tilde O(\kappa)$) with $|S'|=\tilde O((1/\varepsilon)^d)$, one can compute, in $\tilde O(|J|+(1/\varepsilon)^d)$ time, a set of size $\tilde O((1/\varepsilon)^d)$ approximating $\mathcal S(J,[\kappa/\varepsilon,(2d+1)\kappa/(2d\varepsilon)))$ with additive error $\tilde O(\kappa)$ (Definition 2.1).
--
--   Formally: for every $d\ge1$, every admissibility constant $a$ (with $\kappa_d\le a/\varepsilon$) and all constants $C_0,c_0$ of the certificate (error $C_0\kappa_i\,\mathrm{polylog}^{c_0}$, $|S'|\le C_0(1/\varepsilon)^d\mathrm{polylog}^{c_0}$) there are a word-RAM program and constants $b,C,c$ such that on every such input (the jobs, $\kappa$, a $0/1$ word per job marking $J'$, and the list $S'\subseteq\mathbb Q^d_{\ge0}$) and every width $w\ge b(\lfloor\log_2(|J|+M+2)\rfloor+1)$, on every coin sequence the program halts within $C(|J|+(1/\varepsilon)^d)\,\mathrm{polylog}^c$ steps with at most $C(1/\varepsilon)^d\mathrm{polylog}^c$ output vectors approximating the target box with additive error $C\kappa_i\,\mathrm{polylog}^c$; here $\mathrm{polylog}=\log_2(|J|+2)\log_2(2/\varepsilon)$.
--
--   Lemma 5.8 applies it once the level-by-level merging has produced a dense certificate.
--
--   Differences from the source:
--   - reading: "one can compute" on the word RAM → one program of the published randomized word RAM, correct and within time on every coin sequence, at every width $w\ge b(\lfloor\log_2(|J|+M+2)\rfloor+1)$; reason: the paper names no machine; trans-dichotomous convention
--   - reading: the $\tilde O$ of the given certificate and of $|S'|$ → for all constants $C_0,c_0$, chosen before the program; reason: the hidden constants of a hypothesis are arbitrary; the output constants may depend on them
--   - reading: the parameters $\kappa$ of the surrounding partial-profile instance → the standing assumptions $1\le\kappa_1\le\dots\le\kappa_d\le a/\varepsilon$ for a constant $a$, and $d\ge1$; reason: §§4.2–5 fix an admissible partial-profile instance (Definition 3.3); the lemma's own sentence states only the conditions on $J$
--   - encoding: $1/\varepsilon$ a power of two (p.7, the convention of §§3–5) → $\varepsilon=2^{-\ell}$ with $\ell\ge1$, given as the word $\ell$; reason: the paper's own convention for these sections; $\varepsilon<1$
--   - encoding: a dense certificate $(J',S')$ given as input → $J'$ as one $0/1$ word per job occurrence, $S'$ as a list of rational vectors (numerator, denominator per coordinate); reason: the paper fixes no representation
-- source:
--   Lin Chen, Tingwei Hu, Jiayi Lian, Yuchen Mao, Guochuan Zhang, Faster Approximation Schemes for Scheduling on Related Machines, STOC 2027 submission #796 (October 2026), source.pdf SHA-256 5d7d0135eed9cbe942c80598e2bb07d8c56ab67aec0d6e8486a067237654f7f3, p.13, Lemma 5.3 (proof pp.13–14); Definition 5.2 p.13

import Mathlib
import Definitions.Def_MatroidSensOracle_WordRAM
import Definitions.Def_RelatedSchedFPTAS796_Main_Model
import Definitions.Def_RelatedSchedFPTAS796_Main_Machine
import Definitions.Def_RelatedSchedFPTAS796_Main_Problems

set_option autoImplicit false

open MatroidSensOracle MeasureTheory Pointwise

namespace RelatedSchedFPTAS796.Main

/-- **Lemma 5.3**, p.13 (proof pp.13–14). Fix the dimension `d ≥ 1`, the parameter conditions of
the partial-profile problem (`1 ≤ κ_1 ≤ ⋯ ≤ κ_d ≤ a/ε`) and the constants `C₀, c₀` hidden in the
certificate's `Õ`. Let `ε = 2^{−ℓ}` and let `J` be a multiset of integers in `[1/ε, 2/ε)` with
`Σ(J) ≥ ((d+1)/d)∑_j κ_j/ε`. Given a dense certificate `(J', S')` for `J` (Definition 5.2 with
error `C₀κ·polylog^{c₀}`) with `|S'| ≤ C₀(1/ε)^d·polylog^{c₀}`, one can compute in
`Õ(|J| + (1/ε)^d)` time a set of size `Õ((1/ε)^d)` approximating `𝒮(J, [κ/ε, (2d+1)κ/(2dε)))`
with additive error `Õ(κ)`; here `polylog = log₂(|J|+2)·log₂(2/ε)` and the output constants
`C, c` are chosen with the program. -/
theorem lemma_5_3 (d : ℕ) (hd : 1 ≤ d) (a C₀ c₀ : ℕ) : ∃ (P : List Instr) (b C c : ℕ),
    ∀ (ℓ : ℕ) (J : List ℕ) (κ : Fin d → ℚ) (J' : Finset (Fin J.length)) (S' : List (Fin d → ℚ)),
      1 ≤ ℓ → JobsInRange ℓ J → ((d : ℚ) + 1) / d * ((∑ i, κ i) * 2 ^ ℓ) ≤ (J.sum : ℚ) →
      KappaAdmissible a ℓ κ → (∀ x ∈ S', ∀ i, 0 ≤ x i) →
      (S'.length : ℝ) ≤ C₀ * (1 / epsOf ℓ) ^ d * polylog2 J.length (epsOf ℓ) c₀ →
      IsDenseCertificate (epsOf ℓ) (fun i => (κ i : ℝ))
        (fun i => C₀ * (κ i : ℝ) * polylog2 J.length (epsOf ℓ) c₀) (jobsOf J) Finset.univ J'
        (ratToReal '' {x | x ∈ S'}) →
      ∀ w : ℕ, widthMin b J.length (maxWord (certInput ℓ J κ J' S')) ≤ w →
        ∀ ω : Coins, ∃ mem, runFor P w (certInput ℓ J κ J' S')
            (C * ((J.length : ℝ) + (1 / epsOf ℓ) ^ d) * polylog2 J.length (epsOf ℓ) c) ω
              = some mem ∧
          (outCount mem : ℝ) ≤ C * (1 / epsOf ℓ) ^ d * polylog2 J.length (epsOf ℓ) c ∧
          ApproxAdd (partialProfiles d (jobsOf J)) (outRatSet d mem) (partialBox ℓ κ)
            (fun i => C * (κ i : ℝ) * polylog2 J.length (epsOf ℓ) c) := by sorry

end RelatedSchedFPTAS796.Main
