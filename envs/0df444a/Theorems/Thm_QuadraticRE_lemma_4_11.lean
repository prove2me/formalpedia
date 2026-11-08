-- Prove2me | Theorems.Thm_QuadraticRE_lemma_4_11
-- name    : QuadraticRE.lemma_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:21:41.843043+00:00
-- url     : https://prove2.me/theorems/0b2b9519-e7eb-43c7-b365-cae88fe37aec
-- title:
--   Lemma 4.11 — replacing cubic coordinates (both paragraphs)
-- statement:
--   There are a universal constant $K$ and one transformation $T$, computed by a polynomial-time machine from the description of $H$ (including $N$, $r$, $\ell$) and $1^\lambda$, with the following properties for every description of $H:\mathbb F_2^N\times\mathbb F_2^r\to\mathbb F_2^\ell$ by monomials of degree at most three with $M$ terms, and every $\lambda\ge1$. Let $\delta_\lambda$, $\varepsilon_\lambda$ be the errors of $E_\lambda$.
--
--   1. $T$ outputs a description $D'$ of degree at most two and straight-line programs $\mathrm{pre}$, $\mathrm{post}$ of at most $KM\lambda^3$ gates each.
--   2. For every $f$ and decoder $\mathrm{Dec}_H$: if $H$ is $\delta_0$-correct for $f$ with $\mathrm{Dec}_H$, then $D'$ is $(\delta_0+M\delta_\lambda)$-correct for $f$ with $\mathrm{Dec}_H\circ\mathrm{pre}$.
--   3. For every $f$ and simulator law $\mathrm{Sim}_H$: if $H$ is $\varepsilon_0$-private for $f$ with $\mathrm{Sim}_H$, then $D'$ is $(\varepsilon_0+M\varepsilon_\lambda)$-private for $f$ with the simulator that runs $\mathrm{Sim}_H$ and then $\mathrm{post}$ on fresh coins.
--   4. For every family $H_\kappa$ of such descriptions with parameters $\lambda_\kappa$, whose encoded inputs have length polynomial in $\kappa$: if $M_\kappa\varepsilon_{\lambda_\kappa}$ is negligible and $H_\kappa$ is computationally private with simulators $\mathrm{Sim}_\kappa$, then the transformed family is computationally private with the composite simulators.
--
--   So degree three becomes degree two at the price of $M$ copies of $E_\lambda$.
--
--   Differences from the source:
--   - reading: decoding and simulation require the running time of the corresponding algorithms for H plus O(Mλ³) → decoder Dec_H ∘ pre and simulator post ∘ (Sim_H, coins), with pre and post straight-line programs of at most K·M·λ³ gates and H's algorithms black boxes; reason: the bound is on the added work only, as the page says; the page counts field operations and names no machine; an SLP pays for each operation and has no branching, so this is the strong reading (paper.md decision 3)
--   - reading: its expanded polynomial description can be constructed in time polynomial in λ and the description size of H, including N + r + ℓ → one fixed machine of Mathlib's Turing.TM2ComputableInPolyTime, from the bit encoding of the input (all numbers in unary) to the bit encoding of the output, in time polynomial in the input length; reason: Definition 3.7 gives no machine model; the length lemma of the verification file shows the encoded parameters have length between σ+λ and a fixed polynomial in σ+λ (paper.md decision 2)
--   - generalization: H a δ₀-correct, ε₀-private RE ⇒ a (δ₀+Mδ_λ)-correct, (ε₀+Mε_λ)-private RE → correctness and privacy transfer separately; reason: the two together give the page's statement; the separate correctness transfer is also "the same correctness bound" of the second paragraph
--   - generalization: provided all descriptions and running times are polynomially bounded → provided the encoded descriptions with 1^λ have length polynomial in κ; no hypothesis on the running times of H's algorithms; reason: fewer hypotheses; the page's family satisfies them
--   - encoding: δ_λ, ε_λ; M with each zero coordinate one zero term; negligible ν : ℕ → [0,1] → the actual errors of E_λ; numTerms counting an empty coordinate once; negligible without the range [0,1]; reason: same quantities; the range is dropped because Mε_λ can exceed one at small λ, and an advantage lies in [0,1] anyway
--   - encoding: δ₀, ε₀ ∈ [0,1] → arbitrary real bounds; reason: on [0,1] the same notion; the conclusion's bounds may exceed one
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), Lemma 4.11, p.29

import Mathlib
import Definitions.Def_QuadraticRE_IsRE
import Definitions.Def_QuadraticRE_jLam
import Definitions.Def_QuadraticRE_CompPrivate

namespace QuadraticRE

/-- Lemma 4.11 of Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), p.29: replacing cubic coordinates, both paragraphs.

`T` is one transformation, computed by one polynomial-time machine from the description of `H` and
`1^λ`; it does not see `f`, `Dec_H` or `Sim_H`, which are quantified afterwards ("the same
transformation"). `M` is `q.D.numTerms`. The errors `δ_λ`, `ε_λ` are the actual errors of `E_λ`.

**Formalization Note.** Correctness and privacy transfer separately, which implies the transfer of an RE
and is what the second paragraph needs for "the same correctness bound". The overhead `O(Mλ³)` is the
size of the two straight-line programs around `H`'s algorithms, which are black boxes. In the second
paragraph, the polynomial bound is on the descriptions and on `λ_κ` (the encoded input has `λ_κ` in
unary), and on the distinguisher; nothing is needed of `H`'s algorithms beyond this. -/
theorem lemma_4_11 :
    ∃ (K : ℕ) (T : ∀ q : CubicInput, CubicOutput q.N q.ℓ),
      PolyTimeFn encCubicInput (fun q => encCubicOutput (T q)) ∧
      (∀ q : CubicInput,
        (T q).D'.DegLE 2 ∧
        (T q).pre.size ≤ K * (q.D.numTerms * q.lam ^ 3) ∧
        (T q).post.size ≤ K * (q.D.numTerms * q.lam ^ 3) ∧
        (∀ (Y : Type) (f : (Fin q.N → F2) → Y) (δ₀ : ℝ) (DecH : (Fin q.ℓ → F2) → Option Y),
          IsCorrect f q.D.eval δ₀ DecH →
          IsCorrect f (T q).D'.eval (δ₀ + q.D.numTerms * deltaLam q.lam)
            (fun z' => DecH ((T q).pre.eval z'))) ∧
        (∀ (Y : Type) (f : (Fin q.N → F2) → Y) (ε₀ : ℝ) (SimH : Y → (Fin q.ℓ → F2) → ℝ),
          IsPrivate f q.D.eval ε₀ SimH →
          IsPrivate f (T q).D'.eval (ε₀ + q.D.numTerms * epsLam q.lam) ((T q).compSim SimH))) ∧
      (∀ (q : ℕ → CubicInput) (b τ : ℕ → ℕ)
        (f : ∀ κ, (Fin (q κ).N → F2) → Fin (b κ) → F2)
        (sim : ∀ κ, (Fin (b κ) → F2) → (Fin (τ κ) → F2) → Fin (q κ).ℓ → F2)
        (Q : Polynomial ℕ),
        (∀ κ, (encCubicInput (q κ)).length ≤ Q.eval κ) →
        Negligible (fun κ => ((q κ).D.numTerms : ℝ) * epsLam (q κ).lam) →
        CompPrivate (cubicFamily q b τ f sim) →
        CompPrivate (transformedFamily T q b τ f sim)) := by sorry

end QuadraticRE
