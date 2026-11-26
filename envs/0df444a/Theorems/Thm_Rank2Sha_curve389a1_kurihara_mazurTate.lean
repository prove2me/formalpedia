-- Prove2me | Theorems.Thm_Rank2Sha_curve389a1_kurihara_mazurTate
-- name    : Rank2Sha.curve389a1_kurihara_mazurTate
-- status  : Open
-- author  : @barindersbanwait
-- created : 2026-11-25T22:35:47.209966+00:00
-- url     : https://prove2.me/theorems/e96fa910-c2b6-42ac-9718-dee7c016c73d
-- title:
--   Kurihara numbers of 389a1 equal the tame discriminant modulo $p$ (K-MT′)
-- statement:
--   Let $E$ be the elliptic curve $y^2 + y = x^3 + x^2 - 2x$ over $\mathbb{Q}$ (LMFDB 389.a1), with the basis $P_1 = (0,0)$, $P_2 = (-1,1)$ of $E(\mathbb{Q})$. For a prime $p$, a **Kolyvagin prime** for $p$ is a prime $l \ne 389$ with $l \equiv 1 \pmod p$ such that $E(\mathbb{F}_l)[p]$ is cyclic of order $p$. For distinct Kolyvagin primes $l_1, l_2$ for $p$ let
--
--   $$
--   \delta_{l_1 l_2} = \sum_{a \in (\mathbb{Z}/l_1l_2\mathbb{Z})^\times} \Big[ \frac{a}{l_1 l_2} \Big]^+ \lambda_{l_1}(a)\, \lambda_{l_2}(a) \in \mathbb{F}_p
--   $$
--
--   be the Kurihara number and
--
--   $$
--   M(l_1, l_2) = h_{l_1}(P_1,P_1)\,h_{l_2}(P_2,P_2) + h_{l_1}(P_2,P_2)\,h_{l_2}(P_1,P_1) - 2\,h_{l_1}(P_1,P_2)\,h_{l_2}(P_1,P_2) \in \mathbb{F}_p
--   $$
--
--   the tame discriminant. Here $[r]^+$ is the plus modular symbol normalised by $\Omega^+ = \int_{E(\mathbb{R})}|\omega|$, $\lambda_l$ is the discrete logarithm modulo $l$ to the least primitive root, reduced modulo $p$, and $h_l(P,Q) = \lambda_l\big(\tau_l((\#E(\mathbb{F}_l)/p)\,\bar P, \bar Q)\big)$ with $\tau_l$ the Tate–Lichtenbaum pairing $E(\mathbb{F}_l)[p] \times E(\mathbb{F}_l)/p \to \mathbb{F}_l^\times/(\mathbb{F}_l^\times)^p$ (definitions `Rank2Sha_PlusSymbol389`, `Rank2Sha_TatePairing`, `Rank2Sha_Kurihara389`).
--
--   The statement: there is a finite set $S_0$ of primes such that for every prime $p \notin S_0$ and all distinct Kolyvagin primes $l_1, l_2$ for $p$,
--
--   $$
--   \delta_{l_1 l_2} = M(l_1, l_2) \quad \text{in } \mathbb{F}_p .
--   $$
--
--   Status: open. It is a mod $p$ component of Mazur and Tate's Conjecture 4 (Duke Math. J. 54 (1987), (3.1.1)) at the level $l_1 l_2$, with the factor $\#\text{Ш}\cdot\phi\cdot\mathrm{Disc}_S$ of that conjecture written as $C_\infty M(l_1,l_2)$, where $C_\infty = L''(E,1)/(2\Omega^+\mathrm{Reg})$ is $1$ for this curve to $57$ digits. Mazur and Tate's conjecture assumes that $\text{Ш}(E/\mathbb{Q})$ is finite; this statement does not mention $\text{Ш}$.
--
--   Together with the existence of Kolyvagin primes $l_1, l_2$ with $M(l_1,l_2) \ne 0$ (a Chebotarev argument) and C.-H. Kim's Theorem 1.8 (Amer. J. Math. 148 (2026)), the statement implies that the $p$-Selmer group of $E$ has $p^2$ elements, and so $\text{Ш}(E/\mathbb{Q})[p] = 0$, for all but finitely many $p$.
--
--   Numerical evidence: $\delta_{l_1l_2} = M(l_1,l_2)$ on all $178$ pairs computed with PARI/GP and eclib, at $p = 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37$; $163$ of them have $M(l_1,l_2) \ne 0$. Evaluated from the Lean definitions, $\delta_{l_1l_2}$ agrees with those computations on $74$ of these pairs and $M(l_1,l_2)$ on $96$. Modulo $p^2$, with Kolyvagin primes modulo $p^2$, the identity holds on all $78$ pairs computed at $p = 5$ and all $20$ at $p = 7$. At the supersingular prime $p = 107$, $\delta_{l_1l_2} = M(l_1,l_2) = 17$ on the pair $(l_1, l_2) = (369793, 383917)$.
--
--   **Formalization Note** The modular symbol is defined by an explicit table of Manin symbols and the continued-fraction method, not through the newform; its agreement with the integral is a computation, recorded in the definition `Rank2Sha_PlusSymbol389`. Primality of $p$, $l_1$, $l_2$ is an instance argument `[Fact _.Prime]`. The constant $C_\infty = 1$ is built into the statement. Both sides are computable, and agree on the pairs listed above.
-- source:
--   B. Mazur, J. Tate, Refined conjectures of the "Birch and Swinnerton-Dyer type", Duke Math. J. 54 (1987), 711-750, Conjecture 4, (3.1.1), p. 743 ; C.-H. Kim, The structure of Selmer groups and the Iwasawa main conjecture for elliptic curves, Amer. J. Math. 148 (2026), arXiv:2203.12159v6, Theorem 1.8 ; B. Mazur, K. Rubin, Kolyvagin systems, Mem. Amer. Math. Soc. 168 (2004), no. 799, Proposition 3.6.2 ; M. Kurihara, Münster J. Math. 7 (2014)

import Mathlib
import Definitions.Def_Rank2Sha_Kurihara389

namespace Rank2Sha
theorem curve389a1_kurihara_mazurTate :
    ∃ S₀ : Finset ℕ, ∀ (p : ℕ) [Fact p.Prime], p ∉ S₀ →
      ∀ (l₁ l₂ : ℕ) [Fact l₁.Prime] [Fact l₂.Prime], l₁ ≠ l₂ →
        IsKolyvaginPrime p l₁ → IsKolyvaginPrime p l₂ →
          kuriharaNumber389 p l₁ l₂ = tameDiscriminant389 p l₁ l₂ := by sorry
end Rank2Sha
