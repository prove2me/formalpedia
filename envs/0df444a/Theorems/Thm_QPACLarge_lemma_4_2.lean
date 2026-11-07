-- Prove2me | Theorems.Thm_QPACLarge_lemma_4_2
-- name    : QPACLarge.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:09:37.313191+00:00
-- url     : https://prove2.me/theorems/c58998f7-5534-4abb-9707-73d97d355c15
-- title:
--   Lemma 4.2 — subexponentially secure OWFs give a strong PRF with members of circuit size $\le\lambda^d$
-- statement:
--   If subexponentially secure one-way functions exist, then a strong pseudorandom function family exists. In particular, there are a key length $\ell$, an evaluation algorithm, a rational constant $\varepsilon \in (0,1)$ and an integer $d \ge 1$ such that the family satisfies Eq. (7),
--
--   $$
--   \mathrm{Adv}_G(D, \lambda) \le 2^{-\lambda^\varepsilon} \quad\text{for every } D \text{ running in time at most } 2^{\lambda^\varepsilon} \text{ and every large } \lambda,
--   $$
--
--   and every member $g_{\lambda,s}$ of $G_\lambda$ has a Boolean circuit of size at most $\lambda^d$ for all sufficiently large $\lambda$. The paper calls this well known (HILL and GGM) and gives only a sketch; it is what turns the random padded targets of Section 5.2 into polynomial-size ones in Section 5.3.
--
--   Differences from the source:
--   - encoding: uniform randomized algorithms running in time at most $2^{n^\varepsilon}$ (inverters) and $2^{\lambda^\varepsilon}$ (distinguishers) → Turing machines (oracle machines for distinguishers) with that many coins, clocked at $\lfloor 2^{n^\varepsilon}\rfloor$ (resp. $\lfloor 2^{\lambda^\varepsilon}\rfloor$) steps; time in the security parameter; reason: a clocked machine is a machine running in time polynomial in the bound, and $\varepsilon$ is existential on both sides
--   - encoding: a family $G_\lambda$ with a polynomial-time evaluation algorithm and polynomial-time $\ell$ → a key length $\ell$ and an evaluation map $G$ whose first output bit on $1^\lambda 0\,s\,x$ is $g_{\lambda,s}(x)$; $\ell$ computed as $1^\lambda \mapsto 1^{\ell(\lambda)}$; reason: $\ell$ is polynomially bounded, so unary output is polynomial time
--   - reading: every positive polynomial $p$ → $p(n) + 1$ for every $p \in \mathbb N[X]$; reason: every positive polynomial is below some $p + 1$, and every $p + 1$ is positive
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Lemma 4.2 and Definition (Strong PRFs), p.31

import Mathlib
import Definitions.Def_QPACLarge_SubexpOWFExists
import Definitions.Def_QPACLarge_IsStrongPRF
import Definitions.Def_QPACLarge_InSIZE

namespace QPACLarge

open QAlgorithms QAlgorithms.Complexity Filter

/-- **Lemma 4.2 (Strong PRFs from Subexponentially Secure OWFs).**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Lemma 4.2, p.31: "If subexponentially secure one-way functions exist, then a strong
pseudorandom function family exists. In particular, there are a rational constant `ε ∈ (0, 1)` and a
fixed integer `d ≥ 1` such that the family satisfies Equation (7) and every member of `G_λ` has a
Boolean circuit of size at most `λ^d` for all sufficiently large `λ`."

**Formalization Note.** A family is a key length `ℓ` and an evaluation algorithm `G`
(`IsStrongPRF`, `prfEval`); the members of `G_λ` are `g_{λ,s}` for the keys `s ∈ {0,1}^{ℓ(λ)}`. The
paper gives only a proof sketch (HILL + GGM). -/
theorem lemma_4_2 (h : SubexpOWFExists) :
    ∃ (ℓ : ℕ → ℕ) (G : Str → Str) (ε : ℚ) (d : ℕ), IsStrongPRF ℓ G ε ∧ 1 ≤ d ∧
      ∀ᶠ lam : ℕ in atTop, ∀ s : Fin (ℓ lam) → Bool,
        InSIZE (prfEval G lam (List.ofFn s)) (lam ^ d) := by sorry

end QPACLarge
