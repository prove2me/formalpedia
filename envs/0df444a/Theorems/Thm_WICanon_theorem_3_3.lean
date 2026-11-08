-- Prove2me | Theorems.Thm_WICanon_theorem_3_3
-- name    : WICanon.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:06:57.506869+00:00
-- url     : https://prove2.me/theorems/eaa054cc-a1e5-4e7c-b0a8-83dd6377e2ea
-- title:
--   Theorem 3.3 — WI with no WC implies ioAI-OWF
-- statement:
--   Let $\mathcal R$ be an NP relation for which there is no $\varepsilon$-WC for some $\varepsilon\in1/\mathrm{poly}$ [resp., statistically sound $\varepsilon$-WC]. If there exists a constant-round honest-verifier witness-indistinguishable interactive argument [resp., interactive proof] for $\mathcal R$, then infinitely-often auxiliary-input one-way functions exist.
--
--   No derandomization assumption enters here; the cost is that the WC in the hypothesis may have negligible errors.
--
--   **Formalization Note** The argument and the proof variant are two clauses.
--
--   Differences from the source:
--   - reading: negligible δ with every x, w0, w1 and every non-uniform PPT D → for each D a negligible δ_D at all lengths; reason: the literal order lets D depend on x, and a table in the finite control collapses WI to SWI at every x; the reading is the weakest form of the hypothesis
--   - encoding: non-uniform D with advice z_n on inputs of length n → advice and 1^n indexed by n = |x|; reason: |x| is the security parameter of the notion; the view determines no input length in general
--   - reading: for every x ∉ L and every non-uniform PPT prover: acceptance ≤ β(|x|) → each prover is bound from some length on, and it receives x; reason: the literal order lets the prover depend on x and collapses computational to statistical soundness
--   - generalization: PPT A on (a, f_a(x)) → PPT A on (1^n, a, f_a(x)); reason: a machine ignoring 1^n is the printed adversary, so the Lean conclusion implies the printed one
--   - generalization: ε ∈ 1/poly → ε(n) ≥ 1/p(n) with no upper bound; reason: it contains every 1/p
--   - encoding: efficiently computable family indexed by a → one machine on (1^n, a, x); reason: when λ and m are both constant the family is trivially invertible, otherwise n is polynomially readable from the lengths
--   - encoding: states st_V,i, st_P,i and per-round coins → next-message functions of the history, one coin tape per party; reason: a state is computed from the coins and the messages; same protocols
--   - encoding: prover coins polynomial in |x| + |w| → a coin count depending on |x|; reason: witnesses are polynomially bounded and a machine may ignore coins
--   - encoding: a possibly inefficient randomized prover → a deterministic reply function; reason: a randomized prover's acceptance probability is an average over its coins
--   - encoding: P̂ with coins → a non-uniform machine with one coin tape across rounds; reason: a prover keeps its tape; advice per length |x|
--   - reading: A(r) in WC soundness, for every x ∉ L → each adversary receives x and has its own negligible error at all lengths; reason: with advice per length the adversary could not read x; hardwiring the worst instance of each length gives the same notion
-- source:
--   Arnon, Mazor, Pass, Silbak, Does Witness Indistinguishability Require Cryptography?, STOC 2027 submission manuscript (sha256 3f78ec3d…), Theorem 3.3, p.17

import Mathlib
import Definitions.Def_WICanon_PolyBounds
import Definitions.Def_WICanon_IsNPRelation
import Definitions.Def_WICanon_Soundness
import Definitions.Def_WICanon_WitnessIndist
import Definitions.Def_WICanon_WCScheme
import Definitions.Def_WICanon_AIOWF

set_option autoImplicit false

namespace WICanon

/-- **Theorem 3.3** (WI with no WC implies ioAI-OWF). Arnon, Mazor, Pass, Silbak, *Does Witness
Indistinguishability Require Cryptography?*, STOC 2027 submission manuscript (sha256 3f78ec3d…), p.17. Let `R` be
an NP relation for which there is no `ε`-WC for some `ε ∈ 1/poly` [resp., statistically sound `ε`-WC]. If there
exists a constant-round honest-verifier witness indistinguishable interactive argument [resp., interactive proof]
for `R`, then infinitely-often auxiliary-input one-way functions exist.

**Formalization Note.** Two clauses, argument and proof. No derandomization assumption. -/
theorem theorem_3_3 (R : Relation) (q : Polynomial ℕ) (hR : IsNPRelation R q) (ε : ℕ → ℝ)
    (hε : InvPoly ε) :
    (¬ HasWC R ε →
      (∃ (k : ℕ) (pv : Protocol), pv.rounds = (fun _ => k) ∧ IsInteractiveArgument pv R ∧
        HonestWINegl pv R) → IOAIOWFExist) ∧
    (¬ HasStatWC R ε →
      (∃ (k : ℕ) (pv : Protocol), pv.rounds = (fun _ => k) ∧ IsInteractiveProof pv R ∧
        HonestWINegl pv R) → IOAIOWFExist) := by sorry

end WICanon
