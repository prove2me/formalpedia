-- Prove2me | Theorems.Thm_SpatialHalfspace_FullLabels_lemma_2_5
-- name    : SpatialHalfspace.FullLabels.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:28:11.833735+00:00
-- url     : https://prove2.me/theorems/cb44a041-97b9-4448-9383-05f516a6842f
-- title:
--   Lemma 2.5 — Simulation from exact kernels
-- statement:
--   Let $G$ be a $p$-dimensional substrate with terminals $U$, and let the feature marginals $\mu=(\mu_u)_{u\in U}$ on $\mathbb R^D$ have finite support. Let $\Pi$ be a learner of the sample model (terminal $u$ holds an i.i.d. sequence of examples from $P_u$). Then $\Pi$ can be simulated in the exact-kernel model: there is a protocol $\Pi'$ on the same substrate, built from $\mu$ and $\Pi$ only, in which terminal $u$ is given $\eta_{u,x}=P_u(Y=1\mid X=x)$ for $x\in\operatorname{supp}\mu_u$, such that
--
--   1. $\Pi'$ is legal whenever $\Pi$ is, and every classifier output by $\Pi'$ is a classifier output by $\Pi$ on some execution;
--   2. for every $P\in\mathcal E(\mu)$,
--
--   $$\operatorname{Law}_{\Pi'}\big((T_f)_{f\in E_G},\ \hat h\big)\ =\ \operatorname{Law}_{\Pi}\big((T_f)_{f\in E_G},\ \hat h\big).$$
--
--   In particular the simulation has the same expected bit-meter cost and the same success probability, so lower bounds proved in the exact-kernel model hold in the sample model.
--
--   **Formalization Note** Both protocols are required to have measurable transcripts and jointly measurable root classifiers; the law of the classifier is taken on the product σ-algebra of $\{0,1\}^{\mathbb R^D}$ (finite-dimensional distributions).
--
--   Differences from the source:
--
--   - reading: every sample-based learner can be simulated in the exact-kernel model with the same joint distribution of transcripts and outputs → one exact-kernel protocol, chosen from μ and Π before P, that is legal whenever Π is, outputs only classifiers Π can output, and has for every P ∈ E(μ) the same joint law of all edge transcripts and the root classifier; reason: "simulated" means running the same learner on locally generated samples; App. A.1 states that the simulation stays legal and preserves the cost, and the use in Theorem 4.3 needs properness to be preserved
--   - encoding: exact conditional probabilities η_{u,x} for x ∈ supp(μ_u) as local input → the function x ↦ P_u(Y=1|X=x) on atoms of the marginal and 0 elsewhere; reason: μ is known to every participant, so the values off the support carry no information
--   - encoding: learners with expectations and success probabilities → learners with measurable transcripts and a root classifier jointly measurable in inputs, tapes and feature vector; reason: standing measurability convention; without it probabilities and expectations would be undefined
--   - encoding: an informal binary interactive protocol with shared and private tapes → the round model of the Protocol definition: one bit or nothing per direction per edge per round, local latched halting, a finite timed receive history at halting, local finalization that may discard unused receive or timing information, root output from its own input, tapes and final local state, prefix-freeness and cut replay, and almost-sure finite halting at every vertex; reason: finite local halting implements the source’s termination requirement; arbitrary delays and computation are uncharged, messages can be serialized into rounds, and cut replay of final states excludes uncharged timing or control information from affecting the output while allowing unused information to be discarded
--   - encoding: sample-based learners with local access to i.i.d. examples → each local send, halt, finalization, and root-output operation depends on a finite sample prefix, with no uniform bound unless UsesSamples is stated; reason: finite execution can request only finitely many samples; the prefix may depend on the input, tapes and local history, so adaptive sample-based learners are included
--   - generalization: positive feature and physical dimensions and a nonempty finite terminal population → natural dimensions p,D including zero and any finite terminal set, including empty; reason: sample simulation is local and the empty-terminal case only retains input-independent tapes and outputs; restricting to positive dimensions and nonempty terminals recovers every source learner
--   - generalization: probability feature marginals μ_u → arbitrary finite-support measures μ_u, with the simulation guarantee required for every P ∈ E(μ); reason: if any μ_u is not a probability measure then E(μ) is empty; every source marginal tuple is included, and a constant simulator with an output of the original protocol supplies the remaining existential clauses in the empty-environment case
-- source:
--   Yang, Spatial Communication Complexity of Agnostic Halfspace Learning, STOC 2027 submission #119 (2026), preprint, SHA-256 e5822ae144143c29214b0dab09b1a1863f55740d17b6f50ed091ddf8ffcaa692, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/119.pdf, printed p. 6, PDF p. 7, Lemma 2.5, PDF p. 7 (proof in App. A.1, PDF p. 14)

import Definitions.Def_SpatialHalfspace_FullLabels_Construction

open MeasureTheory ProbabilityTheory UnderstandingML
open scoped ENNReal InnerProductSpace

namespace SpatialHalfspace.FullLabels

/-- Lemma 2.5 (Simulation from exact kernels), printed p. 6. Every learner of the sample
model whose terminal feature marginals `μ_u` have finite support is simulated by a protocol of the
exact-kernel model on the same substrate (built from `μ` only): it is legal whenever the original
is, every output it produces is an output of the original, and for every `P ∈ E(μ)` the joint law
of all edge transcripts and the root classifier is the same in both models. -/
theorem lemma_2_5 {p D : ℕ} {U : Type} [Fintype U] (S : Substrate p U)
    (μ : U → Measure (Vec D)) (hμ : ∀ u, ∃ s : Finset (Vec D), μ u (↑s)ᶜ = 0)
    (Pr : Protocol S (SampleInp D) (Vec D → Bool)) (haccess : Pr.FiniteSampleAccess)
    (hPr : Pr.MeasurableTranscripts)
    (hout : Measurable fun q : ((U → SampleInp D) × Pr.Tape) × Vec D => Pr.rootOutput q.1.1 q.1.2 q.2) :
    ∃ Q : Protocol S (KernelInp D) (Vec D → Bool),
      Q.MeasurableTranscripts ∧
      (Measurable fun q : ((U → KernelInp D) × Q.Tape) × Vec D => Q.rootOutput q.1.1 q.1.2 q.2) ∧
      (∀ x R, ∃ x' R', Q.rootOutput x R = Pr.rootOutput x' R') ∧
      ∀ Pt ∈ env μ,
        (Pr.Legal (sampleModel Pt) → Q.Legal (kernelModel Pt)) ∧
        ((kernelModel Pt).prod Q.tapeLaw).map
            (fun xR => ((fun e => Q.transcript xR.1 xR.2 e), Q.rootOutput xR.1 xR.2)) =
          ((sampleModel Pt).prod Pr.tapeLaw).map
            (fun xR => ((fun e => Pr.transcript xR.1 xR.2 e), Pr.rootOutput xR.1 xR.2)) := by sorry

end SpatialHalfspace.FullLabels
