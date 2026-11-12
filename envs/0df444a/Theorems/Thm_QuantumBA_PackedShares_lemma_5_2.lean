-- Prove2me | Theorems.Thm_QuantumBA_PackedShares_lemma_5_2
-- name    : QuantumBA.PackedShares.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:10:47.067989+00:00
-- url     : https://prove2.me/theorems/7a2a6ea9-614e-488f-8701-b52d20ca31c0
-- title:
--   Lemma 5.2 — Disposable-Share Lemma: protected words have latent values
-- statement:
--   Consider QBA:PackedShares with symbolic parameters satisfying the standing assumptions, every transfer block satisfying $D_\ell\ge p_\ell+3\sigma(D_\ell)$. Fix an input vector, an adversary, an epoch, a set $W$ of words of that epoch and a history $h_0$ of positive probability at which every word of $W$ has been dealt by its dealer, honest at the start of the distribution round, and none has been opened. Assume that each word of $W$ is opened in one public round, in which every honest holder measures all its stored registers of the word, and that on every execution extending $h_0$ every word of $W$ is protected at every boundary from $h_0$ up to the end of its last reconstruction (by a requester honest through it). Then on the executions extending $h_0$ each $\omega\in W$ has a latent value $S_\omega\in F$ such that
--
--   (a) for every history $h$ extending $h_0$ and every set $W'\subseteq W$ of words not yet opened at $h$,
--   $$\rho_{S_{W'}E|h}=q^{-|W'|}\sum_s|s\rangle\langle s|\otimes\rho_{E|h};$$
--
--   (b) every requester honest through a reconstruction of $\omega$ obtains $S_\omega$.
--
--   This is the main technical statement of the sharing scheme: repeated disposable transfers preserve privacy against the adversary's whole quantum system and permit consistent classical reconstruction.
--
--   Differences from the source:
--   - encoding: the parameters remain symbolic until Section 6 (b, w, h, committees, forwarding graphs, capacities) → the statement holds for every parameter record X : Ctx satisfying the standing assumptions WellFormed X of §1.1, §3.1, §5.1–§5.2; reason: the standing assumptions of the sections are written as one predicate; nothing beyond them is assumed
--   - encoding: latent values S_ω with ρ_{S_{W′}E|h} = q^{-|W′|} Σ_s |s⟩⟨s| ⊗ ρ_{E|h} and reconstruction to S_ω → a family Λ h s of positive operators on the adversary’s registers, summing to the unnormalized adversary state at h and consistent in trace along histories, with the marginal identity on unopened words and Λ h s = 0 whenever a reconstruction by an honest requester returned a value ≠ s_ω; reason: this is the joint classical–quantum law of the latent values, the history and the adversary’s system
--   - reading: blocks are those whose round has begun by s; a register not consumed by such a block counts as stored, also before delivery → a block of holder u belongs to the circuit at s if its round has begun by s and u, active at the start of that round, transfers the word; its outputs are inputs of the receiver’s block (if the receiver’s block exists and takes that in-edge) or stored at the receiver; reason: the circuit of §5.3 for QBA:PackedShares; a holder corrupted before its round has no block and its stored registers are exposed, which gives the same marks as an exposed block
--   - reading: a word is unopened if no honest holder has measured a register of it → no process honest and active at a round’s honest step before s measured one of its stored registers of the word in that step; reason: honest holders measure only in their opening rounds
-- source:
--   Jan Olkowski, Fast Quantum Byzantine Agreement with Nearly Linear Quantum Communication, STOC 2027 submission #558 (October 2026), source.pdf SHA-256 612d0471810a0aa053891a77995d579d836cc301efd01df8e75c2bbe8ebb5383, p. 26, Lemma 5.2 (PDF p. 27), setting of §5.3 (p. 25, PDF 26)

import Mathlib
import Definitions.Def_QuantumBA_PackedShares_Analysis

namespace QuantumBA.PackedShares

open scoped BigOperators ENNReal Matrix

/-- Lemma 5.2 (Disposable-Share Lemma), for QBA:PackedShares with symbolic parameters. -/
theorem lemma_5_2 {n : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F] (X : Ctx n F)
    (hX : WellFormed X)
    (hdec : ∀ ℓ, hasTransfer X ℓ → X.p ℓ + 3 * X.sigma (X.D ℓ) ≤ X.D ℓ)
    (x : Fin n → Bool) (A : Adv X) (e : ℕ) (W : Finset (ℕ × Lbl))
    (hW : ∀ wd ∈ W, 1 ≤ wd.1 ∧ wd.1 ≤ X.N ∧ wd.2 ∈ arrayLabels X)
    (h₀ : History F) (hpos : PosH X x A h₀)
    -- every word of `W` has been dealt by an honest dealer and none has been opened at `h₀`
    (hdealt : ∀ wd ∈ W, distEnd X e ≤ h₀.length ∧ DealerBlockAt X x A h₀ h₀.length e wd.1 wd.2 ∧
      Unopened X x A h₀ h₀.length e wd.1 wd.2)
    -- setting of §5.3: each word is opened in one public round, in which every honest holder
    -- measures all its stored registers of the word
    (hopen : ∀ ω, IsExecution (qba X) x A X.t ω → prefixH ω h₀.length = h₀ → ∀ wd ∈ W,
      ∀ R R' p p', MeasuresWord X x A (prefixH ω (bnd n R)) R e wd.1 wd.2 p →
        MeasuresWord X x A (prefixH ω (bnd n R')) R' e wd.1 wd.2 p' → R = R')
    (hopenAll : ∀ ω, IsExecution (qba X) x A X.t ω → prefixH ω h₀.length = h₀ → ∀ wd ∈ W,
      ∀ R p, MeasuresWord X x A (prefixH ω (bnd n R)) R e wd.1 wd.2 p →
        ∀ q, q ∉ badAt X x A (prefixH ω (bnd n R)) (startB n R + (n + 1)) →
          (qba X).halted (viewAt X x A (prefixH ω (bnd n R)) (startB n R + (n + 1)) q) = false →
          ∀ r ∈ (storedUse X (viewAt X x A (prefixH ω (bnd n R)) (startB n R + (n + 1)) q)
              (outsE X (viewAt X x A (prefixH ω (bnd n R)) (startB n R + (n + 1)) q) e) e wd.1 wd.2).map Prod.snd,
            r ∈ qbaMeas X (viewAt X x A (prefixH ω (bnd n R)) (startB n R + (n + 1)) q))
    -- protection on every execution extending `h₀`, at every boundary up to the end of the
    -- last reconstruction of the word
    (hprot : ∀ ω, IsExecution (qba X) x A X.t ω → prefixH ω h₀.length = h₀ → ∀ wd ∈ W,
      ∀ k, h₀.length ≤ k →
        (∃ R q, k ≤ bnd n R ∧ q ∉ badAt X x A (prefixH ω (bnd n R)) (bnd n R) ∧
          (ReconValue X (viewAt X x A (prefixH ω (bnd n R)) (bnd n R) q) e R wd.1 wd.2).isSome) →
        Protected X x A (prefixH ω k) k e wd.1 wd.2) :
    LatentValues X x A h₀ e W (fun _ => True) (fun _ _ => True) := by sorry

end QuantumBA.PackedShares
