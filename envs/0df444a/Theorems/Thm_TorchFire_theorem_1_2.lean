-- Prove2me | Theorems.Thm_TorchFire_theorem_1_2
-- name    : TorchFire.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:48:56.202838+00:00
-- url     : https://prove2.me/theorems/e32aa72d-393e-41f7-81a9-c0e7f8d5bbea
-- title:
--   Theorem 1.2 = Theorems 7.7, 7.8, 8.6 — torch-fire is correct, untelegraphable and globally non-proliferating (pinned-down model)
-- statement:
--   Relative to classical oracles, the torch-fire scheme of Construction 7.4 — flames $|F_s\rangle=|A_a\rangle\otimes|K\rangle$ made of a one-shot-signature anchor and a CGS flame, torches $|T_t\rangle$ that are reusable long-message signing states, and the gatekeeping oracle $\Gamma$ — satisfies the following, stated in the pinned-down model of the mission.
--
--   1. **Correctness (Theorem 7.7).** Verification correctness (32) for every polynomially bounded $R\ge0$: $\Pr[\mathrm{TF.Ver}^O(pk,s,F)=1]\ge1-\mathrm{negl}(\lambda)$ for an honestly issued flame. Cloning correctness (33) for every polynomially bounded $R,q$ and every $j\in[R]$: after $q$ successive calls $(T^{(i)},F_{i-1},F_i)\leftarrow\mathrm{TF.Clone}^O(pk,t_j,s,T^{(i-1)},F_{i-1})$ starting from $T^{(0)}=T_j$, all $q+1$ flames verify with probability $1-\mathrm{negl}(\lambda)$.
--   2. **Untelegraphability, even against parties holding torches (Theorem 7.8).** For every polynomially bounded $R$ and every polynomially query-bounded pair $(A_1,A_2)$ with a separable initial state and shared classical randomness, disjoint torch sets, polynomially many spark flames for $A_1$, and classical messages $M$ then $L$,
--   $$\Pr[\mathrm{TELEGRAPH}^{\mathrm{TF}}_{A^O}(1^\lambda,1^R)=1]\le\mathrm{negl}(\lambda)\quad(59).$$
--   3. **Global non-proliferation (Theorem 8.6).** For polynomially bounded $R,m,N$ with $0\le m\le R$ and every polynomially query-bounded adversary $(A_0,A_1,\dots,A_N)$ of Definition 6.2 — $A_0$ receives polynomially many flames and $m$ torches of its choice and splits into $N$ non-communicating parties with arbitrarily entangled quantum registers, each party receiving a fresh challenge flame —
--   $$\Pr[\mathrm{SPLIT}^{\mathrm{TF}}_{A^O}(1^\lambda,1^R,m,N)=1]\le\mathrm{negl}(\lambda)\quad(92):$$
--   no efficient adversary given $m$ torches enables more than $m$ parties to each clone their challenge flame.
--
--   The probabilities are over the oracle and key sampling, the honest procedures' randomness and all measurements; every honest procedure is the explicit oracle circuit of the paper.
--
--   Differences from the source:
--   - generalization: QPT adversaries → oracle algorithms with arbitrary finite workspace and unitaries; only the number of queries is bounded; reason: every QPT oracle algorithm is one with polynomially many queries (p.18); paper.md decision 2
--   - encoding: an oracle collection whose components may answer ⊥ → one combined oracle, answers in the ⊥-flag encoding; reason: paper.md decision 3; same queries and query counts
--   - reading: the interactive game SPLIT in prose (adaptive spark queries, a torch request at any one point) → normal form: v spark flames issued first, one measured request J between two stages of A_0, entangled quantum registers B_i, probability Tr(T_{m+1}(Z_1..Z_N)ρ); reason: paper.md decision 4; simulates every adversary of Definition 6.2 with the same winning probability and query count
--   - reading: the interactive game TELEGRAPH in prose (separable start with shared randomness, adaptive spark queries) → normal form: shared randomness r with an adversary-chosen distribution, each party preparing its state from r; v flames first; messages M then L; reason: paper.md decision 5; finite separable states are finite mixtures of product states
--   - reading: TELEGRAPH^TF step 2, "The adversary specifies disjoint sets J₁, J₂ ⊆ [R]" → J₁(r), J₂(r) fixed disjoint subsets chosen from the shared randomness r, before any query; reason: no channel between the parties exists before step 4, so a set chosen after one party's own queries can only lie in a range fixed by r and disjoint from the other party's range; taking that whole range gives a party more torches, and a party can ignore extra torches, so this normal form simulates every adaptive choice
--   - encoding: polynomially many spark queries → a polynomially bounded spark count v(λ); reason: normal form of the games
--   - encoding: probabilities over oracle sampling, algorithmic randomness and measurement outcomes → averages over the uniform finite oracle sample of Tr(Eρ) for the final cq-state, measurements deferred (Fact 3.1); reason: paper.md decision 6
--   - encoding: the construction for λ ≥ 2 → every parameter at max(λ, 2); reason: paper.md decision 7; equal for λ ≥ 2, and negligibility ignores finitely many λ
--   - encoding: negl(λ) and polynomials → ν ≥ 0 with ν(λ) ≤ λ^{−c} eventually for every c > 0; p(λ) ≤ (λ+2)^c (published PPADSIS.SubexpSIS definitions); reason: paper.md decision 8; equivalent to p.16 for nonnegative ν
--   - encoding: Dig : {0,1}* → {0,1}^L (14) → Dig uniform on {0,1}^{≤ 1+λ+2Lr}; reason: paper.md decision 10; every message signed in torch-fire has length 1+λ+2Lr
--   - reading: TF.GenOracles(1^λ) (Definition 6.1) → TF.GenOracles(1^λ, 1^R) (Construction 7.4 item 1); reason: paper.md decision 11: the oracle T publishes the R torch keys
--   - encoding: polynomially bounded R, m, N with 0 ≤ m ≤ R → functions ℕ → ℕ, each PolyBounded, with m(λ) ≤ R(λ) for every λ; reason: paper.md decision 15
--   - encoding: OSS.Sign with intermediate measurements; U^O_{y,b} obtained from it by Fact 3.1 (Remark 4.12) → the deferred-measurement signing circuit written gate by gate; the zero state of Σ is |⊥⟩; reason: paper.md decisions 6 and 16
--   - encoding: any polynomially bounded ℓ ≥ r + k + 3 (21) → ℓ = r + k + 3; reason: the least allowed value; nothing depends on the choice
--   - reading: Fire.Gen^G: Construction 4.6 with its queries answered through G → the Construction 4.6 circuit; reason: by (22) G(enc(forward, x)) = P(x) and G(enc(inverse, y, u)) = P⁻¹(y, u): the same unitary
--   - generalization: (33): for every j ∈ [R], Pr ≥ 1 − negl(λ) → one negligible bound on max_{j ∈ [R]} (1 − Pr), i.e. uniform in j; reason: the bound of (58) does not depend on j; it implies the statement for every fixed or λ-dependent j
--   - reading: Theorem 1.2 (informal): "there exists a torch-fire scheme satisfying correctness, untelegraphability and global non-proliferation" → Theorems 7.7, 7.8 and 8.6 for Construction 7.4, all clauses; reason: paper.md decision 1: these are the formal theorems the paper proves for its scheme
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Theorem 1.2, p.5; Theorem 7.7, p.55; Theorem 7.8, (59), p.57; Theorem 8.6, (92), p.75; Construction 7.4, pp.52–53; Definitions 6.1, 6.2, 6.4, pp.44–47

import Mathlib
import Definitions.Def_TorchFire_TF_verCorrProb
import Definitions.Def_TorchFire_TF_splitWinProb
import Definitions.Def_TorchFire_TF_telegraphWinProb
import Definitions.Def_PPADSIS_SubexpSIS_Negligible

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model TorchFire.OSS TorchFire.TF PPADSIS.SubexpSIS

namespace TorchFire

/-- **Theorem 1.2** (p.5) at formal strength: **Theorem 7.7** (p.55), **Theorem 7.8** (p.57) and
**Theorem 8.6** (p.75) for Construction 7.4, in the pinned-down model (Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593; paper.md decisions 2–11,
15, 16). Relative to classical oracles, the torch-fire scheme of Construction 7.4 satisfies:

(a) verification correctness (32) for every polynomially bounded `R ≥ 0`, and cloning correctness (33)
    for every polynomially bounded `R, q` and every `j ∈ [R]` (one negligible bound for all `j`);
(b) untelegraphability (59), even against parties holding torches: for every polynomially bounded `R`
    and every polynomially query-bounded adversary pair `(A_1, A_2)` with polynomially many sparks;
(c) global non-proliferation (92): for polynomially bounded `R, m, N` with `0 ≤ m ≤ R` and every
    polynomially query-bounded adversary `(A_0, A_1, …, A_N)` of Definition 6.2 with polynomially many
    sparks, `Pr[SPLIT^TF_{A^O}(1^λ, 1^R, m, N) = 1] ≤ negl(λ)`: no adversary given `m` torches enables more
    than `m` non-communicating parties to each clone a fresh challenge flame. -/
theorem theorem_1_2 :
    (∀ R : ℕ → ℕ, PolyBounded R → Negligible fun lam => 1 - verCorrProb lam (R lam)) ∧
    (∀ R q : ℕ → ℕ, PolyBounded R → PolyBounded q →
      Negligible fun lam => ⨆ j : Fin (R lam), 1 - cloneCorrProb lam (R lam) (q lam) j) ∧
    (∀ R v Q : ℕ → ℕ, PolyBounded R → PolyBounded v → PolyBounded Q →
      ∀ A : (lam : ℕ) → TelegraphAdv lam (R lam) (v lam), (∀ lam, (A lam).QueryBounded (Q lam)) →
        Negligible fun lam => telegraphWinProb (A lam)) ∧
    (∀ R m N v Q : ℕ → ℕ, PolyBounded R → PolyBounded m → PolyBounded N → PolyBounded v →
      PolyBounded Q → (∀ lam, m lam ≤ R lam) →
      ∀ A : (lam : ℕ) → SplitAdv lam (R lam) (m lam) (N lam) (v lam),
        (∀ lam, (A lam).QueryBounded (Q lam)) →
        Negligible fun lam => splitWinProb (A lam)) := by sorry

end TorchFire
