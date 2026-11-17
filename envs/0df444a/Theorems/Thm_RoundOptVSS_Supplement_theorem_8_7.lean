-- Prove2me | Theorems.Thm_RoundOptVSS_Supplement_theorem_8_7
-- name    : RoundOptVSS.Supplement.theorem_8_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:14:43.411201+00:00
-- url     : https://prove2.me/theorems/e4fb3ac5-730b-4a5b-a6ca-e1557a01df3f
-- title:
--   Theorem 8.7 — conditional compiler: a good event of probability $1-\varepsilon$ in the composed execution gives correctness and commitment with error $\varepsilon$ and polynomial local computation
-- statement:
--   Let $\mathbb F\subseteq\mathbb E$ be finite fields and let $\mathsf{kuWSS}$ be a WSS (Definition 4.1, for some error) of broadcast-then-decode type (Definition 6.1) with three sharing rounds, one reconstruction round and key length $\ell$ independent of the input length $h$, whose output function $\mathrm{Out}$ is polynomial-time, and with efficient key search (Definition 7.7). Fix $\lambda\in\mathbb E\setminus\{0\}$ of algebraic degree over $\mathbb F$ larger than $nm$, $m=(n+1)\ell$, and consider the protocol of §8.2 built from $\mathsf{kuWSS}$.
--
--   Suppose that in this composed execution there is an event $\mathcal G$ of probability at least $1-\varepsilon$ on which all $n+1$ instances satisfy properties (a) and (b) of Definition 6.2 for every honest-consistent assignment. Then:
--
--   1. the protocol satisfies correctness and commitment of Definition 4.2 with error at most $\varepsilon$;
--   2. it has three sharing rounds and one reconstruction round;
--   3. its local computation (the reconstruction output, Protocol 9) is polynomial, with a polynomial that depends only on the polynomial bounding $\mathrm{Out}$ and $\mathrm{Search}$ (not on the fields, the scheme or $\lambda$);
--   4. if in addition the composed sharing phase is perfectly private, it is a VSS scheme with error $\varepsilon$.
--
--   Theorem 8.1 is obtained from this by instantiating $\mathsf{kuWSS}$ with the scheme of §7 and supplying $\mathcal G$ (Lemma 8.3) and privacy (Lemma 8.2).
--
--   **Formalization Note** The compiled protocol is `compiled S Search λ`, the hypothesis on $\mathcal G$ is `CompGood`, and the cost model is `RoundOptVSS.Supplement.Cost`; sizes are measured by $n+\kappa+h+\ell$.
--
--   Differences from the source:
--
--   - reading: a WSS of broadcast-then-decode type with efficient key search → any S : BTD with IsWSSOn AdmK S.prot εK (some εK), IsBTDOn AdmK S and IsExactSearchOn AdmK S Search, Out and Search computed in polynomial time (OutComputed, SearchComputed); reason: Definitions 4.1, 6.1 ("Out is a public deterministic polynomial-time function") and 7.7, at the parameter sets AdmK where the scheme is defined
--   - reading: key length independent of the input length → keyLen a function of (n, t, κ) only; reason: the dealer is a role, not a parameter; §8.2 uses one ℓ for all n + 1 instances
--   - encoding: the protocol of Section 8.2 built from kuWSS → compiled S Search λ at the parameter sets compAdm 𝔽 S AdmK λ (AdmK at the root and at every mask instance; λ ≠ 0 of degree over 𝔽 larger than nm); reason: Protocols 8 and 9 with the notation of p.27; instance messages pass through each instance's own cap; no compiled cap
--   - encoding: P_a samples R_a ← 𝔼^m and shares it in O_a → R_a and the coins of P_a's own instance round 1 drawn together; the latter as one uniform value modulo a common multiple of the request products, split into digits; reason: the coin request of the instance may depend on R_a; the law is exactly that of independent uniform coins
--   - reading: an event 𝒢 of probability at least 1 − ε on which all n + 1 instances satisfy (a) and (b) of Definition 6.2 for every honest-consistent assignment → CompGood: ∀ parameters, C, x, sharing adversary, ∃ ρ_0, ρ_1, …, ρ_n functions of the composed honest view, ∀ reconstruction adversary, Pr[every instance satisfies (a) and (b) for every honest-consistent assignment with the actual openings] ≥ 1 − ε; reason: ρ in Definition 6.2 is fixed by the honest views before the reconstruction adversary; an event on which the properties hold exists iff their set has probability ≥ 1 − ε
--   - encoding: three sharing rounds and one reconstruction round → fixed by the type Protocol of the base model; reason: the model has exactly rounds 0, 1, 2 and 3
--   - reading: its local computation is polynomial → ∀ p (the bound of Out and Search) ∃ p' before the fields, the scheme and λ, and one program computing the output map (Protocol 9) within p'(n + κ + h + ℓ + input size) steps on every input; hypotheses on Out and Search measured by the same n + κ + h + ℓ; reason: the proof counts O(n³) searches and O(n²) evaluations of Out, so the bound depends only on p; for one fixed field the condition on λ bounds n, so a field-dependent p' would be void in n; the paper assumes nothing about the size of ℓ, and for the scheme of §7, ℓ = 6(n − 1)(n − 2)
--   - generalization: Out(σ_i, K; τ) → Out receives the party index i together with σ_i; reason: a scheme whose Out ignores i is a special case, so the theorem covers every scheme the page allows
--   - encoding: Protocol 9 on the parties' states → a compiled state that does not hold exactly n + 1 instance states outputs ⊥; reason: never the case for a party after round one, so no execution changes; it keeps the output from reading a default instance state
--   - encoding: correctness and commitment of Definition 4.2 with error at most ε; a VSS scheme → VSSCorrectCommitOn and IsVSSOn at compAdm, probabilities in ℝ≥0∞; reason: IsVSSOn with the trivial predicate is the base IsVSS
-- source:
--   Liu-Zhang, Masserova, Round-Optimal Statistical Verifiable Secret Sharing with Polynomial Complexity, manuscript (2026; STOC 2027 submission, sha256 3a45d95d…), Theorem 8.7 (p.30), with §8.2 (pp.27–28), Definitions 4.1, 4.2, 6.1, 6.2, 7.7 (pp.15, 18–19, 26)

import Mathlib
import Definitions.Def_RoundOptVSS_Model
import Definitions.Def_RoundOptVSS_Supplement_Cost
import Definitions.Def_RoundOptVSS_Supplement_KeyUniform
import Definitions.Def_RoundOptVSS_Supplement_Compiler

open scoped ENNReal

namespace RoundOptVSS

namespace Supplement

/-- **Theorem 8.7** (Conditional compiler), p.30 of Liu-Zhang, Masserova, *Round-Optimal Statistical
Verifiable Secret Sharing with Polynomial Complexity*, manuscript (STOC 2027 submission, sha256
3a45d95d…): let kuWSS be a WSS of broadcast-then-decode type with three sharing rounds, one
reconstruction round, key length independent of the input length, and efficient key search. If in
the composed execution of the protocol of §8.2 built from kuWSS there is an event `G` of probability
at least `1 − ε` on which all `n + 1` instances satisfy (a) and (b) of Definition 6.2 for every
honest-consistent assignment, then the protocol satisfies correctness and commitment of Definition
4.2 with error at most `ε`, has three sharing rounds and one reconstruction round, and its local
computation is polynomial; if in addition the composed sharing phase is perfectly private, it is a
VSS scheme.

**Formalization Note.** kuWSS is any `S : BTD` (key length a function of `(n, t, κ)`, so independent
of `h`) that is a WSS (`IsWSSOn`, for some error `εK`) and of broadcast-then-decode type
(`IsBTDOn`) at its admissible parameters `AdmK`, with an exact key search (`IsExactSearchOn`), and
whose `Out` and `Search` run in polynomial time (`OutComputed`, `SearchComputed`) in the cost model
of `RoundOptVSS.Supplement.Cost`, sizes measured by `n + κ + h + ℓ` (the paper assumes nothing about
the size of `ℓ`; for the scheme of §7, `ℓ = 6(n − 1)(n − 2)`). The rounds are fixed by the type
`Protocol`. The compiled protocol is `compiled S Search λ`, considered at the parameters
`compAdm 𝔽 S AdmK λ` (kuWSS admissible at the root and at every mask instance, and `λ ≠ 0` of
degree over `𝔽` larger than `nm`). The good event is `CompGood` with committed values `ρ_0, …, ρ_n`
that are functions of the composed honest view. "Polynomial local computation" is one program
computing the output map (Protocol 9's local computation) within `p'(n + κ + h + ℓ + input size)`
steps, where the polynomial `p'` depends only on the polynomial `p` bounding `Out` and `Search`: it is
chosen before the fields, the scheme and `λ`. (For one fixed field the condition on `λ` bounds `n`,
so a `p'` allowed to depend on the field would say nothing about the growth in `n`.) -/
theorem theorem_8_7 (p : Polynomial ℕ) :
    ∃ p' : Polynomial ℕ,
      ∀ (𝔽 𝔼 : Type) [Field 𝔽] [Fintype 𝔽] [Field 𝔼] [Fintype 𝔼] [Algebra 𝔽 𝔼]
        (Msg St Op : Type) (S : BTD 𝔼 Msg St Op) (L : BTDLayout 𝔼 Msg St Op) (Search : SearchFn S)
        (AdmK : Params → Prop) (εK : Params → ℝ≥0∞),
        IsWSSOn AdmK S.prot εK → IsBTDOn AdmK S → IsExactSearchOn AdmK S Search →
        ∀ (cOut cSearch : Program),
        OutComputed 𝔽 AdmK S L (fun P => P.n + P.κ + P.h + S.ℓ P) p cOut →
        SearchComputed 𝔽 AdmK S L Search (fun P => P.n + P.κ + P.h + S.ℓ P) p cSearch →
        ∀ (lam : Params → 𝔼) (ε : Params → ℝ≥0∞),
        CompGood S Search lam (compAdm 𝔽 S AdmK lam) ε →
        VSSCorrectCommitOn (compAdm 𝔽 S AdmK lam) (compiled S Search lam) ε ∧
        (∃ code : Program,
          LocalComputation 𝔽 (compAdm 𝔽 S AdmK lam) (compLayout S L lam) (compiled S Search lam)
            (fun P => P.n + P.κ + P.h + S.ℓ P) p' code) ∧
        (PerfectPrivateOn (compAdm 𝔽 S AdmK lam) (compiled S Search lam) →
          IsVSSOn (compAdm 𝔽 S AdmK lam) (compiled S Search lam) ε) := by sorry

end Supplement

end RoundOptVSS
