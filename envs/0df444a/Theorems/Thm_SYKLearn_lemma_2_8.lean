-- Prove2me | Theorems.Thm_SYKLearn_lemma_2_8
-- name    : SYKLearn.lemma_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:15:35.391516+00:00
-- url     : https://prove2.me/theorems/12525b8d-fc5f-4bca-b1a5-eb24fb622831
-- title:
--   Lemma 2.8 — thermal energy: $\log Z_{H_g}(b)\ge cb^2n$ and $-\mathrm{Tr}[\rho_\beta(H_g)H_g]\ge cbn$ for every $\beta\ge b$
-- statement:
--   Let $H_g$ be the SYK Hamiltonian with couplings $g_I\sim\mathcal N(0,\sigma_n^2)$ and write $Z_{H_g}(t)=\mathrm{Tr}[e^{-tH_g}]$ with the normalized trace $\mathrm{Tr}=2^{-n/2}\mathrm{tr}$. There are universal constants $c,N_0>0$ such that, for every even $n\ge N_0$ and every $0<b\le1$, with probability at least $1-2e^{-cb^2n^2}$,
--
--   $$\log Z_{H_g}(b)\ge cb^2n\qquad\text{and}\qquad -\mathrm{Tr}[\rho_\beta(H_g)H_g]\ge cbn\ \text{ for every }\beta\ge b,$$
--
--   where $\rho_\beta(H_g)=e^{-\beta H_g}/\mathrm{Tr}[e^{-\beta H_g}]$.
--
--   The second bound says the thermal energy is extensive at every inverse temperature above $b$. It fixes the sign of the recovered direction (Theorem 3.1) and gives the first-moment bound of the scale experiment (Lemma 4.6).
--
--   **Formalization Note** The partition function uses the normalized trace (with the ordinary trace the first bound would be trivial). $\mathrm{Tr}[\rho_\beta X]=\mathrm{tr}[\sigma X]$ for the physical Gibbs state $\sigma=e^{-\beta H}/\mathrm{tr}\,e^{-\beta H}$. The quantifier "for every $\beta\ge b$" is inside the event.
--
--   Differences from the source:
--   - generalization: the Majorana operators ψ_i of the paper's fixed representation on ℂ^{2^{n/2}} → every Hermitian CAR family Q.γ of a SYKFastMix.FastMixing.Model; reason: the statement is invariant under unitary conjugation, and every CAR family in dimension 2^{n/2} is unitarily equivalent to the paper's, so it specializes to the paper's operators
--   - encoding: g_I i.i.d. N(0, σ_n²), σ_n² = 6/n³ → disorderLaw Q (product of N(0, 6J²/N³)) with the hypothesis Q.J = 1; reason: with J = 1 the law is exactly the paper's; n even and n ≥ 4 come from Model
--   - encoding: with probability at least 1 − x over g → the complement of the good set has (outer) measure at most x; reason: equivalent for measurable events, and no measurability of the event is assumed
-- source:
--   Anshu–Arunachalam–Chen–Hwang, Efficiently Learning SYK Hamiltonians, STOC 2027 submission (held file sha256 5d7d199a…), Lemma 2.8, (22), p.16

import Mathlib
import Definitions.Def_SYKLearn_Basic

noncomputable section
open Matrix MeasureTheory SYKFastMix.FastMixing

namespace SYKLearn

/-- **Lemma 2.8 (Thermal energy)**, p.16 (Anshu–Arunachalam–Chen–Hwang, *Efficiently Learning SYK
Hamiltonians*, STOC 2027 submission, held file sha256 5d7d199a…). Let `H_g = Σ_{|I|=4} g_I Γ_I`
with independent `g_I ∼ N(0, σ_n²)`, and write `Z_{H_g}(t) = Tr[e^{−tH_g}]`. There are universal
constants `c, N₀ > 0` such that, for every even `n ≥ N₀` and every fixed `0 < b ≤ 1`, with
probability at least `1 − 2e^{−cb²n²}`, `log Z_{H_g}(b) ≥ cb²n` and `−Tr[ρ_β(H_g)H_g] ≥ cbn` for
every `β ≥ b` (22).

**Formalization Note.** `Z` is the **normalized** trace `Tr = 2^{−n/2} tr` (`SYKEdge.ntr`); with
the ordinary trace the first bound would hold trivially. `Tr[ρ_β X] = tr[gibbs H β · X]` with the
published physical Gibbs state. The clause "for every `β ≥ b`" is inside the event. The bad event
is bounded in outer measure. `Q.J = 1`; every CAR family. -/
theorem lemma_2_8 :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ (N : ℕ) (Q : Model N), N₀ ≤ N → Q.J = 1 →
      ∀ b : ℝ, 0 < b → b ≤ 1 →
        disorderLaw Q {w | ¬ (c * b ^ 2 * N ≤
            Real.log (SYKEdge.ntr (mexp ((-b : ℂ) • hamiltonian Q w))).re ∧
          ∀ β : ℝ, b ≤ β →
            c * b * N ≤ -(Matrix.trace (gibbs (hamiltonian Q w) β * hamiltonian Q w)).re)} ≤
          ENNReal.ofReal (2 * Real.exp (-(c * b ^ 2 * (N : ℝ) ^ 2))) := by sorry

end SYKLearn
